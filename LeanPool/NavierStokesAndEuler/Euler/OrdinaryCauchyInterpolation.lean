/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerHigherEnergy
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordInterpolation
import LeanPool.NavierStokesAndEuler.Euler.NonnegativeLogConvex
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import LeanPool.NavierStokesAndEuler.Euler.SobolevCauchyInterpolation

/-! Actual ordinary L² convergence upgrades to convergence in every
fixed Sobolev norm under uniform higher-order bounds. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerSmoothFieldSobolevTime EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerSobolevCauchyInterpolation Finset
open scoped ContDiff Topology

local instance instOrdinaryCauchyInterpolation1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem wordMaximum_zero (A : SmoothL2Field Space) : wordMaximum 0 A=‖A.toLp‖ := by
  apply sup'_eq_of_forall
  intro w _
  rfl

theorem tensorNorm_interpolate_zero (A : SmoothL2Field Space) (q : ℕ) (N : ℝ)
    (hN : WordBound (2 * q) N A) :
    tensorNorm q A ≤ wordCount q*Real.sqrt (‖A.toLp‖*N) := by
  apply tensorNorm_le_wordCount
  intro n hn w
  have hp := EulerNonnegativeLogConvex.between (fun j => wordMaximum j A)
    (wordMaximum_nonneg A) (wordMaximum_logconvex A) 0 n n (Nat.zero_le n) (le_refl n)
  simp only [wordMaximum_zero,Nat.sub_zero] at hp
  have hh : ‖(wordField A w).toLp‖^2 ≤ ‖A.toLp‖*N := by
    calc
      _ ≤ (wordMaximum n A)^2 := pow_le_pow_left₀ (norm_nonneg _) (word_norm_le_maximum A w) 2
      _ = wordMaximum n A*wordMaximum n A := pow_two _
      _ ≤ ‖A.toLp‖*wordMaximum (n+n) A := hp
      _ ≤ _ := mul_le_mul_of_nonneg_left (wordMaximum_le hN (by omega)) (norm_nonneg _)
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg (norm_nonneg _) (wordBound_nonneg hN))).mpr hh

theorem ordinarySobolev_norm_le_tensor (A : SmoothL2Field Space) (q : ℕ) :
    ‖ordinarySobolev q A.toLp A.translation_contDiff‖ ≤ tensorNorm q A := by
  apply (ordinarySobolev_norm_le q A.toLp A.translation_contDiff).trans
  apply sum_le_sum
  intro n _
  exact A.norm_iteratedFDeriv_translation_le n 0

variable {T : ℝ}

/-- Field path, given by `⟨fun t => (A t).toLp,continuous_toLp A (hA 0)⟩`. -/
def fieldPath (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : C(Icc (0 : ℝ) T,EulerMeanSolenoidal.L2) :=
  ⟨fun t => (A t).toLp,continuous_toLp A (hA 0)⟩

theorem sobolevPath_norm_le_tensor (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (q : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t, tensorNorm q (A t) ≤ M) : ‖sobolevPath A hA q‖ ≤ M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro t
  exact (ordinarySobolev_norm_le_tensor (A t) q).trans (hb t)

theorem sobolevPath_cauchy_of_l2 (hT : 0 ≤ T)
    (A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q (A k t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (A k) (hA k))) (q : ℕ) :
    CauchySeq (fun k => sobolevPath (A k) (hA k) q) := by
  obtain ⟨M,hM⟩ := hb (q+1)
  have hM0 : 0 ≤ M := (tensorNorm_nonneg (q+1) (A 0 ⟨0,le_rfl,hT⟩)).trans (hM _ _)
  let u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace 1 (q+1)) :=
    fun k => sobolevPath (A k) (hA k) (q+1)
  have hu (k : ℕ) : ‖u k‖ ≤ M := sobolevPath_norm_le_tensor (A k) (hA k) (q+1) M hM0 (hM k)
  let L := ordinaryLift.toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have hl : CauchySeq (fun k => L (fieldPath (A k) (hA k))) := by
    have h := h0.map L.uniformContinuous
    simpa only [CauchySeq,Filter.map_map,Function.comp_def] using h
  have hv (k : ℕ) : (valueOperator 1 (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k) =
      L (fieldPath (A k) (hA k)) := by
    apply ContinuousMap.ext
    intro t
    exact ordinarySobolev_value (q+1) (A k t).toLp (A k t).translation_contDiff
  have hh : CauchySeq (fun k =>
      (valueOperator 1 (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k)) := by
    simpa only [hv] using hl
  have hc := cauchy_restrict_of_value 1 (q := q) (by omega : q < q+1) T M hM0 u hu hh
  have he (k : ℕ) : (restrictOperator 1 (by omega : q ≤ q+1)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (u k)=sobolevPath (A k) (hA k) q := by
    apply ContinuousMap.ext
    intro t
    exact restrict_sobolev (by omega : q ≤ q+1) (A k t)
  simpa only [he] using hc

theorem exists_sobolevPath_limit (hT : 0 ≤ T)
    (A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q (A k t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (A k) (hA k))) (q : ℕ) :
    ∃ p : C(Icc (0 : ℝ) T,SobolevSpace 1 q),
      Tendsto (fun k => sobolevPath (A k) (hA k) q) atTop (𝓝 p) :=
  cauchySeq_tendsto_of_complete (sobolevPath_cauchy_of_l2 hT A hA hb h0 q)

end EulerOrdinarySobolev
