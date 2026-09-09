/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatKernel
public import LeanPool.NavierStokesAndEuler.Euler.CylinderHeatLaplacian
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure

@[expose] public section

/-! A bounded actual Laplacian evaluation and the genuine heat generator on finite Sobolev data. -/

noncomputable section

namespace EulerSobolevHeatGenerator

open MeasureTheory EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerGaussianCylinderHeat EulerMetricHeatEnergy EulerSobolevHeat
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual spatial Laplacian evaluated as a bounded map from Hq to L², q≥2. -/
def laplacianEvaluation (q : ℕ) (hq : 2 ≤ q) : SobolevSpace period q →L[ℝ] LiftL2 period :=
  ∑ i : Fin 4, wordOperator period (⟨⟨2, Nat.lt_succ_of_le hq⟩, fun _ : Fin 2 => i⟩ : SobolevWord q)

/-- The Laplacian evaluation is the sum of the four genuine second derivative coordinates. -/
theorem laplacianEvaluation_apply {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    laplacianEvaluation period q hq u =
      ∑ i : Fin 4, word period u hq (fun _ : Fin 2 => i) := by
  simp only [laplacianEvaluation, sum_apply]
  rfl

/-- The actual Laplacian is bounded by four times the complete Sobolev norm. -/
theorem laplacianEvaluation_bound {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    ‖laplacianEvaluation period q hq u‖ ≤ 4 * ‖u‖ := by
  rw [laplacianEvaluation_apply]
  have h := norm_sum_le (Finset.univ : Finset (Fin 4))
    (fun i => word period u hq (fun _ : Fin 2 => i))
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin 4, ‖u‖ := Finset.sum_le_sum fun i _ =>
      word_norm_le period u ⟨⟨2, Nat.lt_succ_of_le hq⟩, fun _ : Fin 2 => i⟩
    _ = _ := by simp

/-- Bounded Laplacian evaluation agrees exactly with the existing genuine strong-jet Laplacian. -/
theorem laplacianEvaluation_eq_jet {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    laplacianEvaluation period q hq u =
      jetLaplacian period (EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq) := by
  rw [laplacianEvaluation_apply, jetLaplacian]
  apply Finset.sum_congr rfl
  intro i _
  rw [EulerPressureJetIdentities.SpatialJet.word_unique
    (EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq) (toJet period u) rfl le_rfl hq]
  exact (toJet_word period u hq _).symm

/-- The actual Laplacian evaluation commutes with Gaussian heat. -/
theorem laplacianEvaluation_heat {q : ℕ} (hq : 2 ≤ q) (v : ℝ≥0) (u : SobolevSpace period q) :
    laplacianEvaluation period q hq (heatOperator period q v u) =
      cylinderHeat period v (laplacianEvaluation period q hq u) := by
  rw [laplacianEvaluation_apply, laplacianEvaluation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Actual viscous heat on the complete Sobolev space, extended constantly to negative physical time. -/
def heatFlow (q : ℕ) (ν t : ℝ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  heatOperator period q (2 * ν * t).toNNReal

/-- The Sobolev flow has exactly the original genuine L² viscous heat value. -/
@[simp]
theorem heatFlow_value {q : ℕ} (ν t : ℝ) (u : SobolevSpace period q) :
    value period (heatFlow period q ν t u) = viscousCylinderHeat period ν t (value period u) := rfl

/-- Positive-time heat is differentiable in L² with the actual bounded Laplacian evaluation. -/
theorem heatFlow_value_hasDerivAt {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (u : SobolevSpace period q) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => value period (heatFlow period q ν s u))
      (ν • laplacianEvaluation period q hq (heatFlow period q ν t u)) t := by
  have h := viscousCylinderHeat_equation period (EulerH6Pressure.SpatialJet.restrict (toJet period
    u) 2 hq) hν ht
  rw [cylinderHeatJet_laplacian, ← laplacianEvaluation_eq_jet period hq u] at h
  change HasDerivAt (fun s => viscousCylinderHeat period ν s (value period u))
    (ν • laplacianEvaluation period q hq (heatOperator period q (2 * ν * t).toNNReal u)) t
  rw [laplacianEvaluation_heat]
  exact h

/-- The actual L² heat orbit has the half-Laplacian derivative on the nonnegative variance half-line. -/
theorem realHeat_value_hasDerivWithinAt {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => realCylinderHeat period s (value period u))
      ((1 / 2 : ℝ) • realCylinderHeat period t (laplacianEvaluation period q hq u)) (Set.Ici 0) t
        := by
  let J := EulerH6Pressure.SpatialJet.restrict (toJet period u) 2 hq
  by_cases hzero : t = 0
  · subst t
    have h := realCylinderHeat_generator_zero period J
    rw [← laplacianEvaluation_eq_jet period hq u] at h
    simpa only [realCylinderHeat, Real.toNNReal_zero, cylinderHeat_zero] using h
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have h := (realCylinderHeat_generator_pos period J hp).hasDerivWithinAt (s := Set.Ici 0)
    rw [← laplacianEvaluation_eq_jet period hq u] at h
    exact h

/-- The heat orbit is Lipschitz in nonnegative variance with a bound from the actual Hq norm. -/
theorem heat_value_lipschitz {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    LipschitzWith (Real.nnabs (2 * ‖u‖)) (fun v : ℝ≥0 => cylinderHeat period v (value period u)) :=
      by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hb : ∀ t ∈ Set.Ici (0 : ℝ),
      ‖(1 / 2 : ℝ) • realCylinderHeat period t (laplacianEvaluation period q hq u)‖ ≤ 2 * ‖u‖ := by
    intro t _
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h := (cylinderHeat_norm_le period t.toNNReal _).trans (laplacianEvaluation_bound period hq
      u)
    change (1 / 2 : ℝ) * ‖cylinderHeat period t.toNNReal (laplacianEvaluation period q hq u)‖ ≤ _
    linarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => realHeat_value_hasDerivWithinAt period hq u t ht) hb (convex_Ici (0 : ℝ))
    (show (w : ℝ) ∈ Set.Ici 0 from w.property) (show (v : ℝ) ∈ Set.Ici 0 from v.property)
  change dist (cylinderHeat period v (value period u)) (cylinderHeat period w (value period u)) ≤
    (Real.nnabs (2 * ‖u‖) : ℝ) * dist (v : ℝ) (w : ℝ)
  simpa only [realCylinderHeat, Real.toNNReal_coe, dist_eq_norm, Real.coe_nnabs,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg u))] using h

/-- The constantly extended real-variance heat orbit is globally Lipschitz in L². -/
theorem realHeat_value_lipschitz {q : ℕ} (hq : 2 ≤ q) (u : SobolevSpace period q) :
    LipschitzWith (Real.nnabs (2 * ‖u‖)) (fun t : ℝ => realCylinderHeat period t (value period u))
      := by
  simpa only [mul_one, Function.comp_def, realCylinderHeat] using
    (heat_value_lipschitz period hq u).comp Real.lipschitzWith_toNNReal

/-- The actual viscous heat orbit is globally Lipschitz in L², uniformly in time. -/
theorem heatFlow_value_norm_sub_le {q : ℕ} (hq : 2 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (u : SobolevSpace period q) (s t : ℝ) :
    ‖value period (heatFlow period q ν s u) - value period (heatFlow period q ν t u)‖ ≤
      (4 * ν * ‖u‖) * |s - t| := by
  have h := (realHeat_value_lipschitz period hq u).dist_le_mul (2 * ν * s) (2 * ν * t)
  simp only [dist_eq_norm, Real.coe_nnabs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg u))] at h
  change ‖realCylinderHeat period (2 * ν * s) (value period u) -
    realCylinderHeat period (2 * ν * t) (value period u)‖ ≤ _
  have he : |2 * ν * s - 2 * ν * t| = (2 * ν) * |s - t| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * ν)]
  exact h.trans_eq (by rw [he]; ring)

end EulerSobolevHeatGenerator
