/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.WeightedForcingTime
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat
import LeanPool.NavierStokesAndEuler.Euler.TimeLpLinearity
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedTopBlocks
import LeanPool.NavierStokesAndEuler.Euler.TimeLpMap
import LeanPool.NavierStokesAndEuler.Euler.TimeLpStrongOperators
public import LeanPool.NavierStokesAndEuler.Euler.HeatRegularizedPaths
public import LeanPool.NavierStokesAndEuler.Euler.MildTopWord
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators

/-! Actual finite energy families of all required derivative words and their strong weighted limits.
-/

section

/-! The actual lifted gradient and divergence constraints persist under every available strong
derivative word. -/

@[expose] public section

noncomputable section

namespace EulerSobolevWordConstraints

open EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerDivergenceFreeHeat

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine orthogonal lifted gradient projection acting on the complete Sobolev scale. -/
def sobolevGradientProjection (q : ℕ) (κ : ℝ) (m : Vector3) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  liftOperator period q (gradientProjection period κ m)
    (fun a f => (gradientProjection_translation period κ m a f).symm)

/-- Its zeroth coordinate is exactly the original L² orthogonal projection. -/
theorem sobolevGradientProjection_value {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q) :
    value period (sobolevGradientProjection period q κ m u) = gradientProjection period κ m (value
        period u) := rfl

/-- The actual Sobolev gradient projection acts on each genuine derivative coordinate. -/
theorem sobolevGradientProjection_word {q n : ℕ} (hn : n ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (w : Fin n → Fin 4) :
    word period (sobolevGradientProjection period q κ m u) hn w =
      gradientProjection period κ m (word period u hn w) := rfl

/-- A divergence-free Sobolev field has zero Sobolev gradient projection, including all derivatives.
-/
theorem sobolevGradientProjection_zero {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q)
    (hu : value period u ∈ divergenceFreeSpace period κ m) :
    sobolevGradientProjection period q κ m u = 0 := by
  apply value_injective period
  rw [sobolevGradientProjection_value]
  exact (gradientEvaluation_zero_iff period κ m u).mpr hu

/-- Every actual derivative word of a divergence-free field remains divergence-free. -/
theorem word_divergenceFree {q n : ℕ} (hn : n ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (hu : value period u ∈ divergenceFreeSpace period κ m)
    (w : Fin n → Fin 4) : word period u hn w ∈ divergenceFreeSpace period κ m := by
  apply (gradientSpace period κ m).orthogonalProjectionOnto_eq_zero_iff.mp
  apply Subtype.ext
  change gradientProjection period κ m (word period u hn w) = 0
  rw [← sobolevGradientProjection_word period hn κ m u w,
    sobolevGradientProjection_zero period κ m u hu]
  rfl

/-- A genuine gradient field is fixed by the Sobolev gradient projection. -/
theorem sobolevGradientProjection_self {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q)
    (hu : value period u ∈ gradientSpace period κ m) :
    sobolevGradientProjection period q κ m u = u := by
  apply value_injective period
  rw [sobolevGradientProjection_value]
  exact (gradientSpace period κ m).starProjection_eq_self_iff.mpr hu

/-- Every actual derivative word of a lifted pressure gradient remains in the lifted gradient space.
-/
theorem word_gradient {q n : ℕ} (hn : n ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (hu : value period u ∈ gradientSpace period κ m)
    (w : Fin n → Fin 4) : word period u hn w ∈ gradientSpace period κ m := by
  apply (gradientSpace period κ m).starProjection_eq_self_iff.mp
  change gradientProjection period κ m (word period u hn w) = word period u hn w
  rw [← sobolevGradientProjection_word period hn κ m u w,
    sobolevGradientProjection_self period κ m u hu]

end EulerSobolevWordConstraints

end
end

end

section

/-! Every energy-order word of the actual heat-regularized mild solution obeys its genuine L²
differential equation. -/

@[expose] public section

noncomputable section

namespace EulerRegularizedWordEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerMildWordEquation EulerMildTopWord EulerRegularizedTopBlocks
  EulerHeatRegularizedPaths EulerVolterraConvolution EulerMetricHeatEnergy
      EulerSobolevWordConstraints
  EulerDivergenceFreeHeat EulerGaussianCylinderHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A genuinely regularized derivative word as a bounded map from the source Sobolev space into H².
-/
def regularizedWordBlock {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4) :
    SobolevSpace period q →L[ℝ] SobolevSpace period 2 :=
  (boundedWordBlock period 2 m (by omega : 2+m ≤ q+3) w).comp (heatRegularizer period q n)

/-- Every concrete regularized word block commutes with the actual heat semigroup. -/
theorem regularizedWordBlock_heat {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (v : NNReal) (u : SobolevSpace period q) :
    regularizedWordBlock period hm n w (heatOperator period q v u) =
      heatOperator period 2 v (regularizedWordBlock period hm n w u) := by
  change boundedWordBlock period 2 m (by
      omega) w (heatRegularizer period q n (heatOperator period q v u)) = _
  simp only [heatRegularizer_heat, boundedWordBlock_heat]
  rfl

/-- Its underlying field is exactly heat applied to the actual energy-order derivative of the
unregularized state. -/
theorem regularizedWordBlock_value {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (u : SobolevSpace period (q + 1)) :
    value period (regularizedWordBlock period hm n w (truncateOperator period q u)) =
      cylinderHeat period (regularizerVariance n) (word period u hm w) := by
  change value period (boundedWordBlock period 2 m (by omega) w
    (heatRegularizer period q n (truncateOperator period q u))) = _
  rw [boundedWordBlock_value, heatRegularizer_truncate]
  exact heatRegularizer_word period n hm w u

/-- The actual regularized energy-order word path. -/
def regularizedWordPath {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    C(Icc (0 : ℝ) T, SobolevSpace period 2) :=
  mapPath period T ((regularizedWordBlock period hm n w).comp (truncateOperator period q)) u

/-- At depth two the actual Laplacian evaluation is exactly the original genuine jet Laplacian. -/
theorem laplacianEvaluation_two (u : SobolevSpace period 2) :
    laplacianEvaluation period 2 (le_refl 2) u = jetLaplacian period (toJet period u) := by
  rw [laplacianEvaluation_apply, jetLaplacian]
  exact Finset.sum_congr rfl (fun i _ => (toJet_word period u (le_refl 2) (fun _ : Fin 2 =>
      i)).symm)

/-- Every regularized word at the full solution energy order satisfies the actual time PDE, with no
top-order differentiability premise. -/
theorem regularized_word_hasDerivAt {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT (regularizedWordPath period hm n w T u) r))
      (ν • jetLaplacian period (toJet period (regularizedWordPath period hm n w T u ⟨t, ht.1.le,
          ht.2.le⟩)) +
        value period (regularizedWordBlock period hm n w (f ⟨t, ht.1.le, ht.2.le⟩))) t := by
  have h := viscous_mild_block_hasDerivAt period (le_refl 2)
    (regularizedWordBlock period hm n w) (regularizedWordBlock_heat period hm n w)
    ν hν T hT u₀ (fun t _ => f t) (f.continuous.comp continuous_fst) u hsol t ht
  rw [laplacianEvaluation_two] at h
  exact h

/-- Actual energy-order word regularization preserves lifted divergence-freeness. -/
theorem regularized_word_divergenceFree {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (κ : ℝ) (m₀ : Vector3) (u : SobolevSpace period (q + 1))
    (hu : value period u ∈ divergenceFreeSpace period κ m₀) :
    value period (regularizedWordBlock period hm n w (truncateOperator period q u)) ∈
      divergenceFreeSpace period κ m₀ := by
  rw [regularizedWordBlock_value]
  apply (gradientSpace period κ m₀).orthogonalProjectionOnto_eq_zero_iff.mp
  apply Subtype.ext
  change gradientProjection period κ m₀ (cylinderHeat period (regularizerVariance n) (word period u
      hm w)) = 0
  rw [gradientProjection_cylinderHeat]
  have hz : gradientProjection period κ m₀ (word period u hm w) = 0 := by
    have h := (gradientSpace period κ m₀).orthogonalProjectionOnto_eq_zero_iff.mpr
      (word_divergenceFree period hm κ m₀ u hu w)
    exact congrArg Subtype.val h
  rw [hz, map_zero]

end EulerRegularizedWordEquation

end
end

end

section

/-! Concrete forcing for the regularized word PDE and its strong energy-order time limit. -/

section

/-! Strong L²-time convergence of actual energy-order regularized state, source, and pressure words.
-/

section

/-! Exact bounded observations of genuine higher-order Bochner representatives. -/

@[expose] public section

noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Composition of actual bounded spatial maps is composition of their genuine Bochner actions. -/
theorem compLpL_comp (T : ℝ) (A : E →L[ℝ] F) (B : F →L[ℝ] G) (u : TimeLp T E) :
    B.compLpL 2 (timeMeasure T) (A.compLpL 2 (timeMeasure T) u) =
      (B.comp A).compLpL 2 (timeMeasure T) u := by
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (A.compLpL 2 (timeMeasure T) u), A.coeFn_compLpL u,
    (B.comp A).coeFn_compLpL u] with t h1 h2 h3
  rw [h1, h2, h3]
  rfl

/-- A continuous lower-order representative and an actual higher-order time field have identical
bounded observations when the operators agree on restriction. -/
theorem observation_time_eq (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F) (D : F →L[ℝ] G) (W : E →L[ℝ] G)
    (hDA : ∀ x, D (A x) = W x) (u : TimeLp T E) (f : C(Icc (0 : ℝ) T, F))
    (hf : (fun t => A (u t)) =ᵐ[timeMeasure T] extendPath T hT f) :
    pathLp T hT (D.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) = W.compLpL 2 (timeMeasure T) u := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT (D.compLeftContinuous ℝ (Icc (0 : ℝ) T) f), W.coeFn_compLpL u, hf]
    with t h1 h2 h3
  exact h1.trans (((congrArg D h3.symm).trans (hDA (u t))).trans h2.symm)

end EulerTimeLp

end
end

end

@[expose] public section

noncomputable section

namespace EulerRegularizedWordTime

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerMildWordEquation EulerMildTopWord EulerRegularizedWordEquation EulerRegularizedTopBlocks
  EulerHeatRegularizedPaths EulerTimeLp EulerVolterraConvolution EulerGaussianCylinderHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual L² cylinder heat approximation converges on every Bochner L² time field. -/
theorem field_heat_timeLp_tendsto (T : ℝ) (u : TimeLp T (LiftL2 period)) :
    Filter.Tendsto (fun n => (cylinderHeat period (regularizerVariance n)).compLpL 2 (timeMeasure
        T) u)
      Filter.atTop (𝓝 u) := by
  apply strong_operator_timeLp_tendsto T (fun n => cylinderHeat period (regularizerVariance n)) 1
  · intro n x
    simpa only [one_mul] using cylinderHeat_norm_le period (regularizerVariance n) x
  · intro x
    have h := (cylinderHeat_continuous period x).continuousAt.tendsto.comp
        regularizerVariance_tendsto
    simpa only [cylinderHeat_zero, Function.comp_def] using h

/-- An actual regularized energy-order derivative of a continuous low-order source, as an L² time
path. -/
def sourceWordPath {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) : C(Icc (0 : ℝ) T, LiftL2 period) :=
  ((valueOperator period 2).comp (regularizedWordBlock period hm n w)).compLeftContinuous ℝ (Icc (0
      : ℝ) T) f

/-- Source smoothing agrees exactly with heat on a genuinely higher-order Bochner representative,
whenever their lower fields agree almost everywhere. -/
theorem sourceWordPath_time_eq {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (F : TimeLp T (SobolevSpace period (q + 1)))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f) :
    pathLp T hT (sourceWordPath period hm n w T f) =
      (cylinderHeat period (regularizerVariance n)).compLpL 2 (timeMeasure T)
        ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2
            (timeMeasure T) F) := by
  let W := wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))
  let D := (valueOperator period 2).comp (regularizedWordBlock period hm n w)
  have hobs := observation_time_eq T hT (truncateOperator period q) D
    ((cylinderHeat period (regularizerVariance n)).comp W)
    (regularizedWordBlock_value period hm n w) F f hF
  exact hobs.trans (compLpL_comp T W (cylinderHeat period (regularizerVariance n)) F).symm

/-- The actual regularized source words converge strongly at the full energy order using the proved
higher time regularity. -/
theorem sourceWordPath_time_tendsto {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (F : TimeLp T (SobolevSpace period (q + 1)))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f) :
    Filter.Tendsto (fun n => pathLp T hT (sourceWordPath period hm n w T f)) Filter.atTop
      (𝓝 ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2
          (timeMeasure T) F)) := by
  simpa only [sourceWordPath_time_eq period hm _ w T hT f F hF] using
    field_heat_timeLp_tendsto period T
      ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2
          (timeMeasure T) F)

/-- The H¹ restriction of a regularized energy word is literally the corresponding block of the full
maximal-regularity approximation. -/
theorem regularizedWordPath_first_eq {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    (truncateOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedWordPath period hm
        n w T u) =
      (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w).compLeftContinuous ℝ (Icc (0 : ℝ) T)
        (maximalApproximation period q T n u) := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  change value period (truncateOperator period 1 (regularizedWordBlock period hm n w
      (truncateOperator period q (u t)))) =
    value period (boundedWordBlock period 1 m (by omega) w
      (restrictOperator period (by
          omega : 2+q ≤ q+3) (heatRegularizer period q n (truncateOperator period q (u t)))))
  simp only [value_truncateOperator, boundedWordBlock_value]
  change value period (boundedWordBlock period 2 m (by
      omega) w (heatRegularizer period q n (truncateOperator period q (u t)))) = _
  simp only [boundedWordBlock_value]
  rfl

/-- Genuine maximal regularity gives strong H¹ time convergence for every full energy-order
derivative word. -/
theorem regularizedWordPath_first_tendsto {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
        (𝓝 U)) :
    Filter.Tendsto (fun n => pathLp T hT ((truncateOperator period 1).compLeftContinuous ℝ (Icc (0
        : ℝ) T)
      (regularizedWordPath period hm n w T u))) Filter.atTop
      (𝓝 ((boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w).compLpL 2 (timeMeasure T) U)) := by
  let A := boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w
  have h := (A.compLpL 2 (timeMeasure T)).continuous.continuousAt.tendsto.comp hU
  simpa only [regularizedWordPath_first_eq, pathLp_map, Function.comp_def] using h

end EulerRegularizedWordTime

end
end

end

section

/-! Continuous time-path application and its exact Bochner compatibility. -/

@[expose] public section

noncomputable section

namespace EulerTimeLp

open Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual pointwise action of a continuous operator path on a continuous field path. -/
def timePathApply (T : ℝ) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, F) :=
  ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩

/-- The actual continuous-path action has exactly its Bochner multiplier value. -/
theorem pathLp_timePathApply (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT (timePathApply T A u) = timeMultiplier T hT A (pathLp T hT u) :=
  (timeMultiplier_pathLp T hT A u).symm

/-- Strong L² convergence of actual continuous field paths survives a fixed continuous
time-dependent operator. -/
theorem timePathApply_tendsto (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : ℕ → C(Icc (0 : ℝ) T, E)) (U : TimeLp T E)
    (hu : Filter.Tendsto (fun n => pathLp T hT (u n)) Filter.atTop (𝓝 U)) :
    Filter.Tendsto (fun n => pathLp T hT (timePathApply T A (u n))) Filter.atTop
      (𝓝 (timeMultiplier T hT A U)) := by
  have h := (timeMultiplier T hT A).continuous.continuousAt.tendsto.comp hu
  simpa only [pathLp_timePathApply, Function.comp_def] using h

end EulerTimeLp

end
end

end

@[expose] public section

noncomputable section

namespace EulerRegularizedForcingWord

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerMildTopWord EulerRegularizedWordEquation EulerRegularizedWordTime EulerRegularizedTopBlocks
  EulerMetricHeatEnergy EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual transport-pressure forcing in the regularized energy-word PDE. -/
def forcingWordPath {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4) (T : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) : C(Icc (0 : ℝ) T, LiftL2 period) :=
  sourceWordPath period hm n w T f +
    timePathApply T A ((truncateOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (regularizedWordPath period hm n w T u)) + timePathApply T G (sourceWordPath period hm n w T
          p)

/-- The regularized forcing has its literal source-plus-transport-plus-pressure value. -/
theorem forcingWordPath_apply {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4) (T : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : Icc (0 : ℝ) T) :
    forcingWordPath period hm n w T A G u f p t =
      value period (regularizedWordBlock period hm n w (f t)) +
      A t (truncateOperator period 1 (regularizedWordPath period hm n w T u t)) +
      G t (value period (regularizedWordBlock period hm n w (p t))) := rfl

/-- The source-plus-transport-plus-pressure definition gives the exact regularized word equation. -/
theorem forcingWordPath_equation {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4) (T ν : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : Icc (0 : ℝ) T) :
    (ν • jetLaplacian period (toJet period (regularizedWordPath period hm n w T u t)) +
      value period (regularizedWordBlock period hm n w (f t))) +
      A t (truncateOperator period 1 (regularizedWordPath period hm n w T u t)) +
      G t (value period (regularizedWordBlock period hm n w (p t))) =
    forcingWordPath period hm n w T A G u f p t +
      ν • jetLaplacian period (toJet period (regularizedWordPath period hm n w T u t)) := by
  simp only [forcingWordPath_apply]
  abel

/-- The full energy-order regularized word has the actual clamped-path heat derivative at each
interior time. -/
theorem regularized_word_hasDerivAt_clamped {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT (regularizedWordPath period hm n w T u) r))
      (ν • jetLaplacian period (toJet period (extendPath T hT (regularizedWordPath period hm n w T
          u) t)) +
        extendPath T hT (sourceWordPath period hm n w T f) t) t := by
  have h := regularized_word_hasDerivAt period hm n w ν hν T hT u₀ f u hsol t ht
  change HasDerivAt _ (ν • jetLaplacian period (toJet period
    (regularizedWordPath period hm n w T u (projIcc 0 T hT t))) +
      value period (regularizedWordBlock period hm n w (f (projIcc 0 T hT t)))) t
  rw [projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩]
  exact h

/-- The literal forcing obtained from full energy-order source, state, and pressure time fields. -/
def forcingWordTime {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1))) :
    TimeLp T (LiftL2 period) :=
  (wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2 (timeMeasure
      T) F +
    timeMultiplier T hT A ((boundedWordBlock period 1 m (by
        omega : 1+m ≤ 2+q) w).compLpL 2 (timeMeasure T) U) +
    timeMultiplier T hT G ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord
        (q+1))).compLpL 2 (timeMeasure T) P)

/-- The concrete regularized PDE forcing converges strongly at the full energy order by maximal
regularity and the actual higher-order source/pressure representatives. -/
theorem forcingWordPath_time_tendsto {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
        (𝓝 U))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun t => truncateOperator period q (P t)) =ᵐ[timeMeasure T] extendPath T hT p) :
    Filter.Tendsto (fun n => pathLp T hT (forcingWordPath period hm n w T A G u f p)) Filter.atTop
      (𝓝 (forcingWordTime period hm w T hT A G U F P)) := by
  have hs := sourceWordPath_time_tendsto period hm w T hT f F hF
  have ht := timePathApply_tendsto T hT A _ _ (regularizedWordPath_first_tendsto period hm w T hT u
      U hU)
  have hp := timePathApply_tendsto T hT G _ _ (sourceWordPath_time_tendsto period hm w T hT p P hP)
  have h := (hs.add ht).add hp
  simpa only [forcingWordPath, pathLp_add, forcingWordTime] using h

end EulerRegularizedForcingWord

end
end

end

section

/-! The actual energy-order regularized words converge uniformly in time and preserve pressure
closedness. -/

@[expose] public section

noncomputable section

namespace EulerRegularizedWordEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerMildWordEquation EulerMildTopWord EulerHeatRegularizedPaths EulerVolterraConvolution
  EulerSobolevWordConstraints EulerDivergenceFreeHeat EulerGaussianCylinderHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The unregularized energy-order word retained as an actual H⁰ time path. -/
def energyWordPath {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    C(Icc (0 : ℝ) T, SobolevSpace period 0) :=
  mapPath period T (boundedWordBlock period 0 m (by omega : 0+m ≤ q+1) w) u

/-- The actual regularized energy word is exactly the L² value of its genuine H⁰ heat path. -/
theorem regularizedWordPath_heat_value {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    (valueOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedWordPath period hm n
        w T u) =
      (valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T)
        (pathHeat period 0 T (regularizerVariance n) (energyWordPath period hm w T u)) := by
  apply ContinuousMap.ext
  intro t
  change value period (regularizedWordBlock period hm n w (truncateOperator period q (u t))) =
    value period (heatOperator period 0 (regularizerVariance n) (boundedWordBlock period 0 m (by
        omega) w (u t)))
  rw [regularizedWordBlock_value, heatOperator_value, boundedWordBlock_value]

/-- Every actual energy-order word of the regularized mild solution converges uniformly in L² time
paths, including the top order. -/
theorem regularizedWordPath_value_tendsto {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    Filter.Tendsto (fun n => (valueOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (regularizedWordPath period hm n w T u)) Filter.atTop
      (𝓝 ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T) (energyWordPath period hm w
          T u))) := by
  let v := energyWordPath period hm w T u
  have h := (pathHeat_continuous period T v).continuousAt.tendsto.comp regularizerVariance_tendsto
  have hzero : pathHeat period 0 T 0 v = v := by
    apply ContinuousMap.ext
    intro t
    exact heatOperator_zero period (v t)
  rw [hzero] at h
  have hv := ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ)
      T)).continuous.continuousAt.tendsto.comp h
  simpa only [regularizedWordPath_heat_value, Function.comp_def] using hv

/-- Genuine heat smoothing preserves the lifted gradient subspace. -/
theorem cylinderHeat_gradient (κ : ℝ) (m : Vector3) (v : NNReal) (p : LiftL2 period)
    (hp : p ∈ gradientSpace period κ m) : cylinderHeat period v p ∈ gradientSpace period κ m := by
  apply (gradientSpace period κ m).starProjection_eq_self_iff.mp
  change gradientProjection period κ m (cylinderHeat period v p) = cylinderHeat period v p
  rw [gradientProjection_cylinderHeat]
  have hproj : gradientProjection period κ m p = p := (gradientSpace period κ
      m).starProjection_eq_self_iff.mpr hp
  rw [hproj]

/-- Every regularized pressure word stays in the actual lifted gradient space, without assuming an
unregularized derivative of that order. -/
theorem regularizedWordBlock_gradient {q m : ℕ} (hm : m ≤ q + 1) (n : ℕ) (w : Fin m → Fin 4)
    (κ : ℝ) (m₀ : Vector3) (p : SobolevSpace period q)
    (hp : value period p ∈ gradientSpace period κ m₀) :
    value period (regularizedWordBlock period hm n w p) ∈ gradientSpace period κ m₀ := by
  change value period (boundedWordBlock period 2 m (by omega) w (heatRegularizer period q n p)) ∈ _
  rw [boundedWordBlock_value]
  apply word_gradient period (by omega : m ≤ q+3) κ m₀ (heatRegularizer period q n p) _ w
  rw [heatRegularizer_value]
  exact cylinderHeat_gradient period κ m₀ (regularizerVariance n) (value period p) hp

end EulerRegularizedWordEquation

end
end

end

section

/-! Actual finite families of continuous and Bochner time fields, with exact norm-topology
compatibility. -/

@[expose] public section

noncomputable section

namespace EulerTimeFamily

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite family of continuous time paths as the actual continuous family-valued path. -/
def familyPath (T : ℝ) (u : I → C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, I → E) :=
  ⟨fun t i => u i t, continuous_pi (fun i => (u i).continuous)⟩

omit [Fintype I] [NormedSpace ℝ E] in
/-- Bundling actual finite continuous paths is continuous in their uniform topologies. -/
theorem familyPath_continuous (T : ℝ) : Continuous (familyPath (I := I) (E := E) T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_pi
  intro i
  exact continuous_eval.comp (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)

omit [Fintype I] [NormedSpace ℝ E] in
/-- Componentwise uniform path convergence gives uniform convergence of the actual finite family. -/
theorem familyPath_tendsto (T : ℝ) (u : ℕ → I → C(Icc (0 : ℝ) T, E))
    (v : I → C(Icc (0 : ℝ) T, E))
    (hu : ∀ i, Filter.Tendsto (fun n => u n i) Filter.atTop (𝓝 (v i))) :
    Filter.Tendsto (fun n => familyPath T (u n)) Filter.atTop (𝓝 (familyPath T v)) :=
  (familyPath_continuous T).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hu)

/-- A finite family of actual Bochner fields, constructed by the genuine bounded coordinate
injections. -/
def familyTime (T : ℝ) (u : I → TimeLp T E) : TimeLp T (I → E) := by
  classical
  exact ∑ i, (ContinuousLinearMap.single ℝ (fun _ : I => E) i).compLpL 2 (timeMeasure T) (u i)

/-- The Bochner finite-family construction has exactly the componentwise representative almost
everywhere. -/
theorem familyTime_ae (T : ℝ) (u : I → TimeLp T E) :
    (familyTime T u : ℝ → I → E) =ᵐ[timeMeasure T] fun t i => u i t := by
  classical
  have hi (i : I) := (ContinuousLinearMap.single ℝ (fun _ : I => E) i).coeFn_compLpL (u i)
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset I)
    (fun i => (ContinuousLinearMap.single ℝ (fun _ : I => E) i).compLpL 2 (timeMeasure T) (u i)),
    ae_all_iff.mpr hi] with t ht hh
  rw [familyTime, ht]
  calc
    _ = ∑ i : I, Pi.single i (u i t) := Finset.sum_congr rfl (fun i _ => hh i)
    _ = _ := Finset.univ_sum_single _

/-- Strong convergence of each actual component gives strong convergence of the full finite Bochner
family. -/
theorem familyTime_tendsto (T : ℝ) (u : ℕ → I → TimeLp T E) (v : I → TimeLp T E)
    (hu : ∀ i, Filter.Tendsto (fun n => u n i) Filter.atTop (𝓝 (v i))) :
    Filter.Tendsto (fun n => familyTime T (u n)) Filter.atTop (𝓝 (familyTime T v)) := by
  classical
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    ((ContinuousLinearMap.single ℝ (fun _ : I => E) i).compLpL 2 (timeMeasure
        T)).continuous.continuousAt.tendsto.comp (hu i))

/-- Bundling continuous paths and passing to genuine Bochner classes commute exactly. -/
theorem familyTime_pathLp (T : ℝ) (hT : 0 ≤ T) (u : I → C(Icc (0 : ℝ) T, E)) :
    familyTime T (fun i => pathLp T hT (u i)) = pathLp T hT (familyPath T u) := by
  apply Lp.ext
  filter_upwards [familyTime_ae T (fun i => pathLp T hT (u i)),
    ae_all_iff.mpr (fun i => pathLp_ae T hT (u i)), pathLp_ae T hT (familyPath T u)] with t h1 h2 h3
  rw [h1, h3]
  exact funext (fun i => h2 i)

end EulerTimeFamily

end
end

end

@[expose] public section

noncomputable section

namespace EulerRegularizedEnergyFamily

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerRegularizedWordEquation
  EulerRegularizedForcingWord EulerRegularizedTopBlocks EulerTimeFamily EulerTimeLp
      EulerVolterraConvolution
   EulerWeightedForcingTime
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]
variable {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}

/-- A finite actual family of energy-order heat-regularized Sobolev word paths. -/
def regularizedFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (n : ℕ) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (i : α) :
    C(Icc (0 : ℝ) T, β → SobolevSpace period 2) :=
  familyPath T (fun j => regularizedWordPath period (hd i j) n (w i j) T u)

/-- The genuine L² values of the regularized energy-word family. -/
def regularizedValueFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (n : ℕ) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (i : α) :
    C(Icc (0 : ℝ) T, β → LiftL2 period) :=
  familyPath T (fun j => (valueOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    (regularizedWordPath period (hd i j) n (w i j) T u))

/-- The actual original energy-order derivative family as a continuous L² path. -/
def energyValueFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (i : α) :
    C(Icc (0 : ℝ) T, β → LiftL2 period) :=
  familyPath T (fun j => (valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    (energyWordPath period (hd i j) (w i j) T u))

omit [Fintype α] [Fintype β] in
/-- Every actual finite family of regularized derivative values converges uniformly, including its
top order. -/
theorem regularizedValueFamily_tendsto (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (i : α) :
    Filter.Tendsto (fun n => regularizedValueFamily period d w hd n T u i) Filter.atTop
      (𝓝 (energyValueFamily period d w hd T u i)) :=
  familyPath_tendsto T _ _ (fun j => regularizedWordPath_value_tendsto period (hd i j) (w i j) T u)

/-- The actual finite family of regularized forcing words in the differentiated PDE. -/
def regularizedForcingFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (n : ℕ) (T : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) (i : α) :
    C(Icc (0 : ℝ) T, β → LiftL2 period) :=
  familyPath T (fun j => forcingWordPath period (hd i j) n (w i j) T A G u f p)

/-- The limiting actual finite forcing family represented in Bochner L² time. -/
def forcingFamilyTime (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1))) (i
        : α)
        :
    TimeLp T (β → LiftL2 period) :=
  familyTime T (fun j => forcingWordTime period (hd i j) (w i j) T hT A G U F P)

omit [Fintype α] in
/-- Every actual finite forcing family converges strongly by the genuine word-level maximal
regularity argument. -/
theorem regularizedForcingFamily_tendsto (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
        (𝓝 U))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun t => truncateOperator period q (P t)) =ᵐ[timeMeasure T] extendPath T hT p) (i : α) :
    Filter.Tendsto (fun n => pathLp T hT (regularizedForcingFamily period d w hd n T A G u f p i))
        Filter.atTop
      (𝓝 (forcingFamilyTime period d w hd T hT A G U F P i)) := by
  have h := familyTime_tendsto T _ _ (fun j =>
    forcingWordPath_time_tendsto period (hd i j) (w i j) T hT A G u f p U F P hU hF hP)
  simpa only [familyTime_pathLp, regularizedForcingFamily, forcingFamilyTime] using h

/-- Computed weighted forcing paths converge to the actual weighted norm of the limiting PDE forcing
family. -/
theorem regularizedWeightedForcing_tendsto (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (T : ℝ) (hT : 0 ≤ T) (weights : α → C(Icc (0 : ℝ) T, ℝ))
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
        (𝓝 U))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun t => truncateOperator period q (P t)) =ᵐ[timeMeasure T] extendPath T hT p) :
    Filter.Tendsto (fun n => pathLp T hT (weightedForcingPath T weights
      (regularizedForcingFamily period d w hd n T A G u f p))) Filter.atTop
      (𝓝 (weightedForcingTime T hT weights (forcingFamilyTime period d w hd T hT A G U F P))) := by
  have h := weightedForcingTime_tendsto T hT weights _ _
    (regularizedForcingFamily_tendsto period d w hd T hT A G u f p U F P hU hF hP)
  simpa only [weightedForcingTime_pathLp] using h

end EulerRegularizedEnergyFamily
