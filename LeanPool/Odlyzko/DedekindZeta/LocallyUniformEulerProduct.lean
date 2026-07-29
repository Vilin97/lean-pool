/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealEulerProduct
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealLogDeriv
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealSummability
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A dedekind zeta half plane used in the Odlyzko-bound argument. -/
def dedekindZetaHalfPlane : Set ℂ := {s | 1 < s.re}

lemma isOpen_dedekindZetaHalfPlane : IsOpen dedekindZetaHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

theorem multipliableLocallyUniformlyOn_primeIdealFactor :
    MultipliableLocallyUniformlyOn
      (primeIdealFactor K) dedekindZetaHalfPlane := by
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 1 < s.re at hs
  let δ : ℝ := (s.re - 1) / 2
  let σ : ℝ := (s.re + 1) / 2
  have hδ : 0 < δ := by grind
  have hσ : 1 < σ := by grind
  refine ⟨Metric.closedBall s δ, ?_, ?_⟩
  · exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Metric.closedBall s δ, Metric.closedBall_mem_nhds s hδ,
        Set.inter_subset_left⟩
  · have hu :
        Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
          2 * (primeIdealNorm K P : ℝ) ^ (-σ)) :=
      (summable_primeIdealNorm_rpow K hσ).mul_left 2
    have hbound :
        ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          ∀ z ∈ Metric.closedBall s δ,
            ‖primeIdealFactor K P z - 1‖ ≤
              2 * (primeIdealNorm K P : ℝ) ^ (-σ) := by
      filter_upwards [] with P z hz
      apply norm_primeIdealFactor_sub_one_le K P hσ
      have hdist : dist z s ≤ δ := Metric.mem_closedBall.mp hz
      have hre : |(z - s).re| ≤ dist z s := by
        simpa [dist_eq, norm_sub_rev] using Complex.abs_re_le_norm (z - s)
      dsimp [δ] at hdist
      dsimp [σ]
      rw [Complex.sub_re] at hre
      grind
    simpa only [add_sub_cancel] using
      Summable.multipliableUniformlyOn_one_add
        (ProperSpace.isCompact_closedBall s δ) hu hbound
        (fun P z hz ↦ by
          have hdist : dist z s ≤ δ := Metric.mem_closedBall.mp hz
          have hre : |(z - s).re| ≤ dist z s := by
            simpa [dist_eq, norm_sub_rev] using Complex.abs_re_le_norm (z - s)
          dsimp [δ] at hdist
          rw [Complex.sub_re] at hre
          have hzσ : σ ≤ z.re := by grind
          change ContinuousWithinAt
            (localFactor (primeIdealNorm K P) - fun _ ↦ 1)
              (Metric.closedBall s δ) z
          exact ((hasDerivAt_localFactor (one_lt_primeIdealNorm K P)
            (hσ.trans_le hzσ |> zero_lt_one.trans)).continuousAt.sub
              continuousAt_const).continuousWithinAt)

end NumberField.Odlyzko
