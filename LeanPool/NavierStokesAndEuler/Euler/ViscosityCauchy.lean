/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionViscosityStability

@[expose] public section

/-! Genuine Cauchy convergence of uniformly bounded nonlinear viscous corrections in continuous
  cylinder L². -/

noncomputable section

namespace EulerViscosityCauchy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerCorrectionStabilityBudget EulerCorrectionViscosityStability
open scoped Topology

/-- An actual Lipschitz comparison transfers Cauchy convergence between normed-valued sequences. -/
theorem cauchySeq_of_norm_le {X : Type*} [NormedAddCommGroup X]
    (u : ℕ → X) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : CauchySeq a)
    (hbound : ∀ m n, ‖u m-u n‖ ≤ C*|a m-a n|) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hd : 0 < ε/(C+1) := div_pos hε (by linarith)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp ha (ε/(C+1)) hd
  refine ⟨N,fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have hdist : |a m-a n| < ε/(C+1) := by simpa only [Real.dist_eq] using hN m hm n hn
  have h := mul_le_mul_of_nonneg_left hdist.le hC
  have hlast : C*(ε/(C+1)) < ε := by
    have hh : C/(C+1) < 1 := (div_lt_one (by linarith : 0 < C+1)).mpr (by linarith)
    have hm := mul_lt_mul_of_pos_right hh hε
    calc
      C*(ε/(C+1)) = (C/(C+1))*ε := by ring
      _ < 1*ε := hm
      _ = ε := one_mul ε
  exact (hbound m n).trans_lt (h.trans_lt hlast)

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine continuous L² path underlying a finite-Sobolev correction path. -/
def valuePath {q : ℕ} (T : ℝ) (u : C(Icc (0 : ℝ) T,SobolevSpace period q)) :
    C(Icc (0 : ℝ) T,LiftL2 period) :=
  (valueOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- The actual pointwise comparison controls the full continuous L² path norm. -/
theorem correction_viscosity_norm {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T)) (B : StabilityBudget period hT D)
    (ν μ : ℝ) (hν : 0 < ν) (hμ : 0 < μ) (hν1 : ν ≤ 1)
    (u v : C(Icc (0 : ℝ) T,SobolevSpace period (q+1))) (R : ℝ)
    (huR : ‖u‖ ≤ R) (hvR : ‖v‖ ≤ R)
    (hu : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl (D.coefficients period hq) 0 u t)
    (hv : ∀ t, v t = quadraticDuhamel period μ hμ hT le_rfl (D.coefficients period hq) 0 v t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ t, value period (u t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hvd : ∀ t, value period (v t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ‖valuePath period T u-valuePath period T v‖ ≤ B.comparisonConstant period R*|ν-μ| := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (B.comparisonConstant_nonneg period R) (abs_nonneg
    _))).mpr
  exact correction_viscosity_pointwise period hq T hT D B ν μ hν hμ hν1 u v R huR hvR hu hv hz hud
    hvd

/-- Every actual uniformly Sobolev-bounded correction family with Cauchy viscosities is Cauchy in continuous cylinder L².
Both the nonlinear difference equation and its metric estimate are proved internally. -/
theorem correction_family_cauchy {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T)) (B : StabilityBudget period hT D)
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n) (hν1 : ∀ n, ν n ≤ 1) (hνc : CauchySeq ν)
    (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period (q+1))) (R : ℝ)
    (huR : ∀ n, ‖u n‖ ≤ R)
    (hu : ∀ n t, u n t = quadraticDuhamel period (ν n) (hν n) hT le_rfl (D.coefficients period hq)
      0 (u n) t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ n t, value period (u n t) ∈ divergenceFreeSpace period D.κ D.direction) :
    CauchySeq (fun n => valuePath period T (u n)) := by
  apply cauchySeq_of_norm_le _ ν (B.comparisonConstant period R) (B.comparisonConstant_nonneg
    period R) hνc
  intro m n
  exact correction_viscosity_norm period hq T hT D B (ν m) (ν n) (hν m) (hν n) (hν1 m)
    (u m) (u n) R (huR m) (huR n) (hu m) (hu n) hz (hud m) (hud n)

end EulerViscosityCauchy
