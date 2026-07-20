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
    rw [← MeasureTheory.setLIntegral_univ (μ := μ) (f := fun c : Rand => innerBC b c)]
    exact MeasureTheory.setLIntegral_congr (μ := μ) (f := fun c : Rand => innerBC b c)
      Iio_one_ae_eq_univ.symm
  simp_rw [hInner]
  have hOuter :
      (∫⁻ b : Rand, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        ∫⁻ b in (Set.Iio (1 : Rand) : Set Rand),
          ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    rw [← MeasureTheory.setLIntegral_univ (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)]
    exact MeasureTheory.setLIntegral_congr (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
      Iio_one_ae_eq_univ.symm
  rw [hOuter]
  -- Split the `b`-integral into the four regions.
  have hs_t : MeasurableSet (Set.Iio t : Set Rand) := by simp
  have hsplit_t :=
    (MeasureTheory.lintegral_inter_add_sdiff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
      (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) hs_t)
  have hAint_t : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t :=
    Set.ext fun b => ⟨fun hb => hb.2, fun hb =>
      ⟨by simpa using lt_trans (show (b : ℝ) < t from hb) t_lt_one, hb⟩⟩
  have hAdiff_t : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) :=
    Set.ext fun b => ⟨fun ⟨hb1, hbt⟩ => ⟨le_of_not_gt hbt, hb1⟩,
      fun hb => ⟨hb.2, not_lt_of_ge hb.1⟩⟩
  have hsplit_t' :
      (∫⁻ b in (Set.Iio (1 : Rand) : Set Rand),
          ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        (∫⁻ b in Set.Iio t, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) +
          ∫⁻ b in Set.Ico t (1 : Rand),
            ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    simpa [hAint_t, hAdiff_t] using hsplit_t.symm
  have hs_t2 : MeasurableSet (Set.Iio t2 : Set Rand) := by simp
  have hsplit_t2 :=
    (MeasureTheory.lintegral_inter_add_sdiff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
      (A := (Set.Iio t : Set Rand)) (B := (Set.Iio t2 : Set Rand)) hs_t2)
  have hAint_t2 : ((Set.Iio t : Set Rand) ∩ Set.Iio t2) = Set.Iio t2 :=
    Set.ext fun b => ⟨fun hb => hb.2, fun hb => ⟨lt_trans hb t2_lt_t, hb⟩⟩
  have hAdiff_t2 : ((Set.Iio t : Set Rand) \ Set.Iio t2) = Set.Ico t2 t :=
    Set.ext fun b => ⟨fun ⟨hbt, hb2⟩ => ⟨le_of_not_gt hb2, hbt⟩,
      fun hb => ⟨hb.2, not_lt_of_ge hb.1⟩⟩
  have hsplit_t2' :
      (∫⁻ b in Set.Iio t, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        (∫⁻ b in Set.Iio t2, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) +
          ∫⁻ b in Set.Ico t2 t,
            ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    simpa [hAint_t2, hAdiff_t2] using hsplit_t2.symm
  have hs_t1 : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
  have hsplit_t1 :=
    (MeasureTheory.lintegral_inter_add_sdiff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
      (A := (Set.Iio t2 : Set Rand)) (B := (Set.Iio t1 : Set Rand)) hs_t1)
  have hAint_t1 : ((Set.Iio t2 : Set Rand) ∩ Set.Iio t1) = Set.Iio t1 :=
    Set.ext fun b => ⟨fun hb => hb.2, fun hb => ⟨lt_trans hb t1_lt_t2, hb⟩⟩
  have hAdiff_t1 : ((Set.Iio t2 : Set Rand) \ Set.Iio t1) = Set.Ico t1 t2 :=
    Set.ext fun b => ⟨fun ⟨hb2, hb1⟩ => ⟨le_of_not_gt hb1, hb2⟩,
      fun hb => ⟨hb.2, not_lt_of_ge hb.1⟩⟩
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
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

lemma p_recursive3ParamAlg_lt :
    ClassicalAlgorithm.p recursive3ParamAlg < ENNReal.ofReal (24118 / 100000 : ℝ) := by
  rw [p_recursive3ParamAlg_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

theorem exists_algorithm_p_lt :
    ∃ alg : ClassicalAlgorithm, ClassicalAlgorithm.p alg < ENNReal.ofReal (24118 / 100000 : ℝ) :=
  ⟨recursive3ParamAlg, p_recursive3ParamAlg_lt⟩

end Recursive3Param
end UpperBound

end Distributed2Coloring
