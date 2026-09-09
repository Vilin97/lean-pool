/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MildEquationBridge
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks

@[expose] public section

/-! Every available finite derivative word of the actual viscous mild solution satisfies its
  differentiated L² equation. -/

noncomputable section

namespace EulerMildWordEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerVolterraConvolution EulerDuhamelDifferentiation
  EulerMildEquationBridge EulerSobolevWordBlocks
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Applying a bounded linear spatial map to an actual continuous Sobolev time path. -/
def mapPath {p q : ℕ} (T : ℝ) (A : SobolevSpace period q →L[ℝ] SobolevSpace period p)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) : C(Icc (0 : ℝ) T, SobolevSpace period p) :=
  ⟨fun t => A (u t), A.continuous.comp u.continuous⟩

/-- Every bounded heat-commuting spatial map commutes with the actual Duhamel integral. -/
theorem map_duhamel {p q : ℕ} (A : SobolevSpace period q →L[ℝ] SobolevSpace period p)
    (hA : ∀ v u, A (heatOperator period q v u) = heatOperator period p v (A u))
    (ν T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) :
    A (duhamel period ν T hT f t) = duhamel period ν T hT (mapPath period T A f) t := by
  unfold duhamel
  rw [← A.intervalIntegral_comp_comm ((shiftedHeat_continuous period ν T hT f t).intervalIntegrable
    0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact hA _ _

/-- The gained-kernel mild formula implies the ordinary Duhamel formula at the lower Sobolev order. -/
theorem viscous_mild_truncated_formula {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1))
    (F : Icc (0 : ℝ) T → SobolevSpace period (q + 1) → SobolevSpace period q)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q + 1) => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q + 1) (2 * ν * t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r)))))
    (t : Icc (0 : ℝ) T) :
    truncateOperator period q (u t) = heatFlow period q ν t.val (truncateOperator period q u₀) +
      duhamel period ν T hT (pathNonlinearity T F hF u) t.val := by
  let f := pathNonlinearity T F hF u
  have hc := truncate_heatConvolution period ν hν T hT f t
  rw [convolution_eq_interval T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t] at hc
  rw [hsol t, map_add, truncate_heatOperator]
  change heatFlow period q ν t.val (truncateOperator period q u₀) +
    truncateOperator period q (∫ r in (0 : ℝ)..t.val,
      heatKernel period q ν hν r (extendPath T hT f (t.val-r))) = _
  rw [hc]

/-- Any bounded heat-commuting derivative block of the constructed mild solution satisfies its actual L² evolution. -/
theorem viscous_mild_block_hasDerivAt {p q : ℕ} (hp : 2 ≤ p)
    (A : SobolevSpace period q →L[ℝ] SobolevSpace period p)
    (hA : ∀ v u, A (heatOperator period q v u) = heatOperator period p v (A u))
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T) (u₀ : SobolevSpace period (q + 1))
    (F : Icc (0 : ℝ) T → SobolevSpace period (q + 1) → SobolevSpace period q)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q + 1) => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q + 1) (2 * ν * t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r)))))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (A (truncateOperator period q (extendPath T hT u r))))
      (ν • laplacianEvaluation period p hp (A (truncateOperator period q (u ⟨t, ht.1.le,
        ht.2.le⟩))) +
        value period (A (F ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le, ht.2.le⟩)))) t := by
  let f := pathNonlinearity T F hF u
  let v := mapPath period T (A.comp (truncateOperator period q)) u
  have hv : ∀ s : Icc (0 : ℝ) T, v s = heatFlow period p ν s.val (A (truncateOperator period q u₀))
    +
      duhamel period ν T hT (mapPath period T A f) s.val := by
    intro s
    change A (truncateOperator period q (u s)) = _
    rw [viscous_mild_truncated_formula period ν hν T hT u₀ F hF u hsol s, map_add, map_duhamel
      period A hA]
    congr 1
    exact hA _ _
  exact ordinary_mild_hasDerivAt period hp ν hν T hT (A (truncateOperator period q u₀))
    (mapPath period T A f) v hv t ht

/-- The actual derivative block of a field with enough total Sobolev regularity. -/
def availableWordBlock {q n : ℕ} (h : n + 2 ≤ q) (w : Fin n → Fin 4) :
    SobolevSpace period q →L[ℝ] SobolevSpace period 2 :=
  (wordBlock period 2 n w).comp (restrictOperator period (by omega : 2+n ≤ q))

/-- This available block is exactly the chosen derivative word as an L² field. -/
theorem availableWordBlock_value {q n : ℕ} (h : n + 2 ≤ q) (w : Fin n → Fin 4)
    (u : SobolevSpace period q) :
    value period (availableWordBlock period h w u) = word period u (by omega : n ≤ q) w := by
  change value period (wordBlock period 2 n w (restrictOperator period (by omega : 2+n ≤ q) u)) = _
  rw [wordBlock_value]
  rfl

/-- Actual derivative-word blocks commute with heat, including the endpoint at zero variance. -/
theorem availableWordBlock_heat {q n : ℕ} (h : n + 2 ≤ q) (w : Fin n → Fin 4)
    (v : ℝ≥0) (u : SobolevSpace period q) :
    availableWordBlock period h w (heatOperator period q v u) =
      heatOperator period 2 v (availableWordBlock period h w u) := by
  apply value_injective period
  rw [availableWordBlock_value, heatOperator_value, availableWordBlock_value]
  rfl

/-- Truncation preserves every derivative coordinate still within its range. -/
theorem word_truncate_coordinate {q n : ℕ} (hn : n ≤ q) (w : Fin n → Fin 4)
    (u : SobolevSpace period (q+1)) :
    word period (truncateOperator period q u) hn w = word period u (Nat.le_trans hn (Nat.le_succ
      q)) w := rfl

/-- Every finite derivative word below the source's Sobolev margin obeys the differentiated L² equation. -/
theorem viscous_mild_word_hasDerivAt {q n : ℕ} (h : n + 2 ≤ q) (w : Fin n → Fin 4)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T) (u₀ : SobolevSpace period (q + 1))
    (F : Icc (0 : ℝ) T → SobolevSpace period (q + 1) → SobolevSpace period q)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q + 1) => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q + 1) (2 * ν * t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r)))))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => word period (extendPath T hT u r) (by omega : n ≤ q+1) w)
      (ν • laplacianEvaluation period 2 (by norm_num)
        (availableWordBlock period h w (truncateOperator period q (u ⟨t, ht.1.le, ht.2.le⟩))) +
        word period (F ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le, ht.2.le⟩)) (by omega : n ≤ q) w) t :=
          by
  have hd := viscous_mild_block_hasDerivAt period (by norm_num : 2 ≤ 2)
    (availableWordBlock period h w) (availableWordBlock_heat period h w)
    ν hν T hT u₀ F hF u hsol t ht
  simpa only [availableWordBlock_value, word_truncate_coordinate] using hd

end EulerMildWordEquation
