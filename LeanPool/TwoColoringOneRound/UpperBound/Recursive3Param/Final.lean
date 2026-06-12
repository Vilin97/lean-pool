/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.UpperBound.Recursive3Param.Regions
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
## Final upper bound for the 3-parameter recursive algorithm

This file combines the four `b`-regions computed in
`Distributed2Coloring/UpperBound/Recursive3Param/Regions.lean` and
`Distributed2Coloring/UpperBound/Recursive3Param/Bound.lean` to get an exact rational value for
`ClassicalAlgorithm.p recursive3ParamAlg`, and derives the numerical bound
`ClassicalAlgorithm.p recursive3ParamAlg < 24118/100000`.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval ENNReal

namespace UpperBound
namespace Recursive3Param


lemma p_recursive3ParamAlg_eq :
    ClassicalAlgorithm.p recursive3ParamAlg = ENNReal.ofReal (94835 / 393216 : ℝ) := by
  classical
  -- Start from the reduction to a 2D integral of `innerBC`.
  have hp :
      ClassicalAlgorithm.p recursive3ParamAlg =
        ∫⁻ b : Rand, ∫⁻ c : Rand, innerBC b c ∂μ ∂μ := by
    simpa [μ] using p_eq_lintegral_innerBC
  rw [hp]
  -- Replace both integrals over `Rand` by set integrals over `b,c < 1` (a.e. equal to `univ`).
  have hInner :
      (fun b : Rand => (∫⁻ c : Rand, innerBC b c ∂μ)) =
        fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ := by
    funext b
    calc
      (∫⁻ c : Rand, innerBC b c ∂μ) =
          ∫⁻ c in (Set.univ : Set Rand), innerBC b c ∂μ := by simp
      _ = ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ := by
          exact
            (MeasureTheory.setLIntegral_congr (μ := μ) (f := fun c : Rand => innerBC b c)
              Iio_one_ae_eq_univ.symm)
  simp_rw [hInner]
  have hOuter :
      (∫⁻ b : Rand, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        ∫⁻ b in (Set.Iio (1 : Rand) : Set Rand),
          ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    calc
      (∫⁻ b : Rand, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
          (∫⁻ b in (Set.univ : Set Rand),
              ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) := by simp
      _ =
          ∫⁻ b in (Set.Iio (1 : Rand) : Set Rand),
            ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
          exact
            (MeasureTheory.setLIntegral_congr (μ := μ)
              (f := fun b : Rand =>
                ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
              Iio_one_ae_eq_univ.symm)
  rw [hOuter]
  -- Split the `b`-integral into the four regions.
  have hs_t : MeasurableSet (Set.Iio t : Set Rand) := by simp
  have hsplit_t :=
    (MeasureTheory.lintegral_inter_add_diff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
      (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) hs_t)
  have hAint_t : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t := by
    ext b
    constructor
    · intro hb
      exact hb.2
    · intro hb
      have hb1 : (b : ℝ) < 1 := lt_trans (show (b : ℝ) < t from hb) t_lt_one
      exact ⟨by simpa using hb1, hb⟩
  have hAdiff_t : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) := by
    ext b
    constructor
    · rintro ⟨hb1, hbt⟩
      exact ⟨le_of_not_gt hbt, hb1⟩
    · intro hb
      exact ⟨hb.2, not_lt_of_ge hb.1⟩
  have hsplit_t' :
      (∫⁻ b in (Set.Iio (1 : Rand) : Set Rand),
          ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        (∫⁻ b in Set.Iio t, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) +
          ∫⁻ b in Set.Ico t (1 : Rand),
            ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    simpa [hAint_t, hAdiff_t] using hsplit_t.symm
  have hs_t2 : MeasurableSet (Set.Iio t2 : Set Rand) := by simp
  have hsplit_t2 :=
    (MeasureTheory.lintegral_inter_add_diff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
      (A := (Set.Iio t : Set Rand)) (B := (Set.Iio t2 : Set Rand)) hs_t2)
  have hAint_t2 : ((Set.Iio t : Set Rand) ∩ Set.Iio t2) = Set.Iio t2 := by
    ext b
    constructor
    · intro hb
      exact hb.2
    · intro hb
      exact ⟨lt_trans hb t2_lt_t, hb⟩
  have hAdiff_t2 : ((Set.Iio t : Set Rand) \ Set.Iio t2) = Set.Ico t2 t := by
    ext b
    constructor
    · rintro ⟨hbt, hb2⟩
      exact ⟨le_of_not_gt hb2, hbt⟩
    · intro hb
      exact ⟨hb.2, not_lt_of_ge hb.1⟩
  have hsplit_t2' :
      (∫⁻ b in Set.Iio t, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        (∫⁻ b in Set.Iio t2, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) +
          ∫⁻ b in Set.Ico t2 t,
            ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    simpa [hAint_t2, hAdiff_t2] using hsplit_t2.symm
  have hs_t1 : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
  have hsplit_t1 :=
    (MeasureTheory.lintegral_inter_add_diff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
      (A := (Set.Iio t2 : Set Rand)) (B := (Set.Iio t1 : Set Rand)) hs_t1)
  have hAint_t1 : ((Set.Iio t2 : Set Rand) ∩ Set.Iio t1) = Set.Iio t1 := by
    ext b
    constructor
    · intro hb
      exact hb.2
    · intro hb
      exact ⟨lt_trans hb t1_lt_t2, hb⟩
  have hAdiff_t1 : ((Set.Iio t2 : Set Rand) \ Set.Iio t1) = Set.Ico t1 t2 := by
    ext b
    constructor
    · rintro ⟨hb2, hb1⟩
      exact ⟨le_of_not_gt hb1, hb2⟩
    · intro hb
      exact ⟨hb.2, not_lt_of_ge hb.1⟩
  have hsplit_t1' :
      (∫⁻ b in Set.Iio t2, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        (∫⁻ b in Set.Iio t1, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) +
          ∫⁻ b in Set.Ico t1 t2,
            ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    simpa [hAint_t1, hAdiff_t1] using hsplit_t1.symm
  -- Substitute the splits and the precomputed region values.
  rw [hsplit_t', hsplit_t2', hsplit_t1']
  rw [lintegral_b_below_t1_value, lintegral_b_t1_t2_value, lintegral_b_t2_t_value,
    lintegral_b_above_t_value]
  -- Combine the four `ofReal` values into one exact rational.
  have h0a : 0 ≤ (99 / 1024 : ℝ) := by norm_num
  have h0b : 0 ≤ (68705 / 1572864 : ℝ) := by norm_num
  have h0c : 0 ≤ (13689 / 524288 : ℝ) := by norm_num
  have h0d : 0 ≤ (153 / 2048 : ℝ) := by norm_num
  have hadd1 :
      ENNReal.ofReal (99 / 1024 : ℝ) + ENNReal.ofReal (68705 / 1572864 : ℝ) =
        ENNReal.ofReal ((99 / 1024 : ℝ) + (68705 / 1572864 : ℝ)) := by
    symm
    exact ENNReal.ofReal_add h0a h0b
  have hadd2 :
      ENNReal.ofReal (13689 / 524288 : ℝ) + ENNReal.ofReal (153 / 2048 : ℝ) =
        ENNReal.ofReal ((13689 / 524288 : ℝ) + (153 / 2048 : ℝ)) := by
    symm
    exact ENNReal.ofReal_add h0c h0d
  have hadd3 :
      ENNReal.ofReal ((99 / 1024 : ℝ) + (68705 / 1572864 : ℝ)) +
          ENNReal.ofReal ((13689 / 524288 : ℝ) + (153 / 2048 : ℝ)) =
        ENNReal.ofReal
          (((99 / 1024 : ℝ) + (68705 / 1572864 : ℝ)) +
            ((13689 / 524288 : ℝ) + (153 / 2048 : ℝ))) := by
    symm
    have h0ab : 0 ≤ (99 / 1024 : ℝ) + (68705 / 1572864 : ℝ) := add_nonneg h0a h0b
    have h0cd : 0 ≤ (13689 / 524288 : ℝ) + (153 / 2048 : ℝ) := add_nonneg h0c h0d
    exact ENNReal.ofReal_add h0ab h0cd
  have hrat :
      (((99 / 1024 : ℝ) + (68705 / 1572864 : ℝ)) + ((13689 / 524288 : ℝ) + (153 / 2048 : ℝ))) =
        (94835 / 393216 : ℝ) := by
    norm_num
  have hgroup :
      ENNReal.ofReal (99 / 1024 : ℝ) + ENNReal.ofReal (68705 / 1572864 : ℝ) +
            ENNReal.ofReal (13689 / 524288 : ℝ) + ENNReal.ofReal (153 / 2048 : ℝ) =
        (ENNReal.ofReal (99 / 1024 : ℝ) + ENNReal.ofReal (68705 / 1572864 : ℝ)) +
          (ENNReal.ofReal (13689 / 524288 : ℝ) + ENNReal.ofReal (153 / 2048 : ℝ)) := by
    simp [add_assoc]
  calc
    ENNReal.ofReal (99 / 1024 : ℝ) + ENNReal.ofReal (68705 / 1572864 : ℝ) +
          ENNReal.ofReal (13689 / 524288 : ℝ) + ENNReal.ofReal (153 / 2048 : ℝ) =
        (ENNReal.ofReal (99 / 1024 : ℝ) + ENNReal.ofReal (68705 / 1572864 : ℝ)) +
          (ENNReal.ofReal (13689 / 524288 : ℝ) + ENNReal.ofReal (153 / 2048 : ℝ)) := hgroup
    _ =
        ENNReal.ofReal ((99 / 1024 : ℝ) + (68705 / 1572864 : ℝ)) +
          ENNReal.ofReal ((13689 / 524288 : ℝ) + (153 / 2048 : ℝ)) := by
          simp [hadd1, hadd2]
    _ =
        ENNReal.ofReal
          (((99 / 1024 : ℝ) + (68705 / 1572864 : ℝ)) +
            ((13689 / 524288 : ℝ) + (153 / 2048 : ℝ))) := by
          exact hadd3
    _ = ENNReal.ofReal (94835 / 393216 : ℝ) := by
          rw [hrat]

lemma p_recursive3ParamAlg_lt :
    ClassicalAlgorithm.p recursive3ParamAlg < ENNReal.ofReal (24118 / 100000 : ℝ) := by
  have hp : ClassicalAlgorithm.p recursive3ParamAlg = ENNReal.ofReal (94835 / 393216 : ℝ) :=
    p_recursive3ParamAlg_eq
  rw [hp]
  have hq : 0 < (24118 / 100000 : ℝ) := by norm_num
  have hlt : (94835 / 393216 : ℝ) < (24118 / 100000 : ℝ) := by norm_num
  exact (ENNReal.ofReal_lt_ofReal_iff hq).2 hlt

theorem exists_algorithm_p_lt :
    ∃ alg : ClassicalAlgorithm, ClassicalAlgorithm.p alg < ENNReal.ofReal (24118 / 100000 : ℝ) := by
  refine ⟨recursive3ParamAlg, p_recursive3ParamAlg_lt⟩

end Recursive3Param
end UpperBound

end Distributed2Coloring
