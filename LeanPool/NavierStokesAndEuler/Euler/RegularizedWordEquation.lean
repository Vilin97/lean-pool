/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HeatRegularizedPaths
public import LeanPool.NavierStokesAndEuler.Euler.MildTopWord
import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat
import LeanPool.NavierStokesAndEuler.Euler.RegularizedTopBlocks
import LeanPool.NavierStokesAndEuler.Euler.SobolevWordConstraints

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
  rw [heatRegularizer_heat, boundedWordBlock_heat]
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
