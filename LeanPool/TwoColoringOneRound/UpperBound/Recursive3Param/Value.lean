/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.UpperBound.Recursive3Param.ComputeP
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
Exact computation of `ClassicalAlgorithm.p recursive3ParamAlg`.

The final result is the dyadic rational value
`94835 / 393216 ≈ 0.24117787679 < 24118/100000`.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval

namespace UpperBound
namespace Recursive3Param


open scoped ENNReal

-- The remainder of this file will:
-- 1. Prove piecewise formulas for `innerBC` for our concrete dyadic parameters.
-- 2. Evaluate the resulting iterated integrals as an exact rational.

lemma aSlice_eq_of_t2_le_b_lt_t {b c : Rand} (hb1 : t2 ≤ b) (hb2 : b < t) :
    aSlice b c = if c < t2 then Set.Iic t else if c < t then Set.Iio t2 else ∅ := by
  classical
  ext a
  have hbIcc : (b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) := ⟨le_trans t1_le_t2 hb1, hb2.le⟩
  have hbIio2 : ¬ ((b : ℝ) ∈ Set.Iio (t2 : ℝ)) := by simp [Set.mem_Iio, hb1]
  have hbIci : ¬ ((b : ℝ) ∈ Set.Ici (t : ℝ)) := by simp [Set.mem_Ici, not_le_of_gt hb2]
  have hz0 :
      z0 a b =
        if (a : ℝ) < t2 then (t : ℝ) else if (a : ℝ) ≤ t then (t2 : ℝ) else 0 := by
    by_cases ha2 : (a : ℝ) < t2
    · by_cases haIcc : (a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)
      · have haIio : (a : ℝ) ∈ Set.Iio (t2 : ℝ) := ha2
        simp [z0, haIcc, hbIcc, hbIio2, ha2, haIio]
      · have haIci : ¬ ((a : ℝ) ∈ Set.Ici (t : ℝ)) := by
          have : (a : ℝ) < t := lt_trans ha2 t2_lt_t
          simp [Set.mem_Ici, not_le_of_gt this]
        have hle : ((a : ℝ), (b : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by
          exact show (a : ℝ) ≤ b from le_trans ha2.le hb1
        simp [z0, zBase, haIcc, hbIcc, hbIci, ha2, haIci, hle]
    · have ha2' : t2 ≤ (a : ℝ) := le_of_not_gt ha2
      by_cases hat : (a : ℝ) ≤ t
      · have haIcc : (a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) := ⟨le_trans t1_le_t2 ha2', hat⟩
        have haIio : ¬ ((a : ℝ) ∈ Set.Iio (t2 : ℝ)) := by simp [Set.mem_Iio, ha2]
        simp [z0, haIcc, hbIcc, hbIio2, ha2, haIio, hat]
      · have ht' : (t : ℝ) < a := lt_of_not_ge hat
        have haIcc : ¬ ((a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)) := by
          simp [Set.mem_Icc, (not_le_of_gt ht')]
        have haIci : (a : ℝ) ∈ Set.Ici (t : ℝ) := by simp [Set.mem_Ici, ht'.le]
        simp [z0, zBase, haIcc, hbIcc, hbIci, ha2, haIci, hat]
  by_cases hc : c < t2
  · have hcR : (c : ℝ) < t2 := hc
    have hct : (c : ℝ) < t := lt_trans hcR t2_lt_t
    have hR : a ∈ (if c < t2 then Set.Iic t else if c < t then Set.Iio t2 else ∅) ↔ a ≤ t := by
      simp [hc]
    have hL : a ∈ aSlice b c ↔ a ≤ t := by
      change ((c : ℝ) < z0 a b) ↔ a ≤ t
      rw [hz0]
      constructor
      · intro hca
        by_contra hat
        have ht' : (t : ℝ) < a := lt_of_not_ge hat
        have : (c : ℝ) < 0 := by
          have ha2 : ¬ (a : ℝ) < t2 := not_lt_of_ge (le_trans t2_le_t ht'.le)
          have hat' : ¬ (a : ℝ) ≤ t := not_le_of_gt ht'
          simpa [ha2, hat'] using hca
        exact (not_lt_of_ge (show (0 : ℝ) ≤ c from c.property.1) this)
      · intro hat
        by_cases ha2 : (a : ℝ) < t2
        · simpa [ha2] using hct
        · have hat' : (a : ℝ) ≤ t := hat
          simpa [ha2, hat'] using hcR
    exact (hL.trans hR.symm)
  · have hc' : ¬ c < t2 := hc
    by_cases hct : c < t
    · have hR : a ∈ (if c < t2 then Set.Iic t else if c < t then Set.Iio t2 else ∅) ↔ a < t2 := by
        simp [hc', hct]
      have hL : a ∈ aSlice b c ↔ a < t2 := by
        change ((c : ℝ) < z0 a b) ↔ (a : ℝ) < t2
        rw [hz0]
        constructor
        · intro hca
          by_contra ha2
          have hz0expr_le_t2 :
              (if (a : ℝ) < t2 then (t : ℝ)
                else if (a : ℝ) ≤ t then (t2 : ℝ)
                else 0) ≤ (t2 : ℝ) := by
            have ht20 : (0 : ℝ) ≤ t2 := t2.property.1
            by_cases hat : (a : ℝ) ≤ t <;> simp [ha2, hat, ht20]
          have : (c : ℝ) < t2 := lt_of_lt_of_le hca hz0expr_le_t2
          exact hc' (show c < t2 from this)
        · intro ha2
          have hctR : (c : ℝ) < t := hct
          simpa [ha2] using hctR
      exact (hL.trans hR.symm)
    · have hct' : ¬ c < t := hct
      have hR : a ∈ (if c < t2 then Set.Iic t else if c < t then Set.Iio t2 else ∅) ↔ False := by
        simp [hc', hct']
      have hL : a ∈ aSlice b c ↔ False := by
        change ((c : ℝ) < z0 a b) ↔ False
        constructor
        · intro hca
          have hz0_le : z0 a b ≤ t := by
            rw [hz0]
            by_cases ha2 : (a : ℝ) < t2
            · simp [ha2]
            · by_cases hat : (a : ℝ) ≤ t
              · simpa [ha2, hat] using (t2_le_t : (t2 : ℝ) ≤ t)
              · simpa [ha2, hat] using (t.property.1 : (0 : ℝ) ≤ t)
          have : (c : ℝ) < t := lt_of_lt_of_le hca hz0_le
          exact hct' (show c < t from this)
        · intro hf
          exact False.elim hf
      exact (hL.trans hR.symm)

lemma aSlice_eq_of_t_lt_b {b c : Rand} (hb : t < b) :
    aSlice b c = if c < t then Set.univ else if (c : ℝ) < 1 then Set.Iio t else ∅ := by
  classical
  ext a
  have hbIcc : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)) := by simp [Set.mem_Icc, not_le_of_gt hb]
  have hbIci : (b : ℝ) ∈ Set.Ici (t : ℝ) := by simp [Set.mem_Ici, hb.le]
  have hz0 : z0 a b = if (a : ℝ) < t then 1 else (t : ℝ) := by simp [z0, zBase, hbIcc, hbIci]
  by_cases hct : c < t
  · have hR : a ∈ (if c < t then Set.univ else if (c : ℝ) < 1 then Set.Iio t else ∅) ↔ True := by
      simp [hct]
    have hL : a ∈ aSlice b c ↔ True := by
      change ((c : ℝ) < z0 a b) ↔ True
      rw [hz0]
      have hc1 : (c : ℝ) < 1 := lt_trans (show (c : ℝ) < t from hct) t_lt_one
      by_cases hat : (a : ℝ) < t <;> simp [hat, hct, hc1]
    exact (hL.trans hR.symm)
  · have hct' : ¬ c < t := hct
    by_cases hc1 : (c : ℝ) < 1
    · have hR : a ∈ (if c < t then Set.univ else if (c : ℝ) < 1 then Set.Iio t else ∅) ↔ a < t := by
        simp [hct', hc1]
      have hL : a ∈ aSlice b c ↔ a < t := by
        change ((c : ℝ) < z0 a b) ↔ (a : ℝ) < t
        rw [hz0]
        constructor
        · intro hca
          by_contra hat
          have : (c : ℝ) < t := by simpa [hat] using hca
          exact hct (show c < t from this)
        · intro hat
          simp [hat, hc1]
      exact (hL.trans hR.symm)
    · have hc1' : ¬ (c : ℝ) < 1 := hc1
      have hR : a ∈ (if c < t then Set.univ else if (c : ℝ) < 1 then Set.Iio t else ∅) ↔ False := by
        simp [hct', hc1']
      have hL : a ∈ aSlice b c ↔ False := by
        change ((c : ℝ) < z0 a b) ↔ False
        rw [hz0]
        constructor
        · intro hca
          have : (c : ℝ) < 1 := by
            have hzle : (if (a : ℝ) < t then (1 : ℝ) else t) ≤ 1 := by
              by_cases hat : (a : ℝ) < t <;> simp [hat, (le_of_lt t_lt_one)]
            exact lt_of_lt_of_le hca hzle
          exact hc1' this
        · intro hf
          exact False.elim hf
      exact (hL.trans hR.symm)

private lemma z0_eq_of_t1_le_b_lt_t2 {a b : Rand} (hb1 : t1 ≤ b) (hb2 : b < t2) :
    z0 a b =
      if (a : ℝ) < t1 then (t : ℝ)
      else if (a : ℝ) ≤ b then (t2 : ℝ)
      else if (a : ℝ) < t2 then (b : ℝ)
      else if (a : ℝ) ≤ t then (t1 : ℝ)
      else 0 := by
  have hbt : (b : ℝ) < t := lt_trans hb2 t2_lt_t
  have hbIcc : (b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) := ⟨hb1, hbt.le⟩
  have hbIio2 : (b : ℝ) ∈ Set.Iio (t2 : ℝ) := hb2
  have hbIci : ¬ ((b : ℝ) ∈ Set.Ici (t : ℝ)) := by simp [Set.mem_Ici, not_le_of_gt hbt]
  by_cases ha1 : (a : ℝ) < t1
  · have haIcc : ¬ ((a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)) := by
      simp [Set.mem_Icc, (not_le_of_gt ha1)]
    have haIci : ¬ ((a : ℝ) ∈ Set.Ici (t : ℝ)) := by
      have : (a : ℝ) < t := lt_trans ha1 (lt_trans t1_lt_t2 t2_lt_t)
      simp [Set.mem_Ici, not_le_of_gt this]
    have hle : ((a : ℝ), (b : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by
      exact show (a : ℝ) ≤ b from le_trans ha1.le hb1
    simp [z0, zBase, haIcc, hbIcc, hbIci, ha1, haIci, hle]
  · have ha1' : t1 ≤ (a : ℝ) := le_of_not_gt ha1
    by_cases hab : (a : ℝ) ≤ b
    · have hat2 : (a : ℝ) < t2 := lt_of_le_of_lt hab hb2
      have haIcc : (a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) := ⟨ha1', le_trans hab hbt.le⟩
      have haIci2 : ¬ ((a : ℝ) ∈ Set.Ici (t2 : ℝ)) := by simp [Set.mem_Ici, not_le_of_gt hat2]
      simp [z0, haIcc, hbIcc, hbIio2, ha1, hab, haIci2]
    · by_cases hat2 : (a : ℝ) < t2
      · have haIcc : (a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) := ⟨ha1', le_trans hat2.le t2_le_t⟩
        have haIci2 : ¬ ((a : ℝ) ∈ Set.Ici (t2 : ℝ)) := by simp [Set.mem_Ici, not_le_of_gt hat2]
        simp [z0, haIcc, hbIcc, hbIio2, ha1, hab, hat2, haIci2]
      · have hat2' : t2 ≤ (a : ℝ) := le_of_not_gt hat2
        by_cases hat : (a : ℝ) ≤ t
        · have haIcc : (a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) := ⟨le_trans t1_le_t2 hat2', hat⟩
          have haIio2 : ¬ ((a : ℝ) ∈ Set.Iio (t2 : ℝ)) := by simp [Set.mem_Iio, hat2]
          have haIci2 : (a : ℝ) ∈ Set.Ici (t2 : ℝ) := by simp [Set.mem_Ici, hat2']
          simp [z0, haIcc, hbIcc, hbIio2, ha1, hab, hat2, hat, haIci2]
        · have ht' : (t : ℝ) < a := lt_of_not_ge hat
          have haIcc : ¬ ((a : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)) := by simp [Set.mem_Icc, hat]
          have haIci : (a : ℝ) ∈ Set.Ici (t : ℝ) := by simp [Set.mem_Ici, ht'.le]
          simp [z0, zBase, haIcc, hbIcc, hbIci, ha1, hab, hat2, hat, haIci]

private lemma mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_t1 {a b c : Rand}
    (hb1 : t1 ≤ b) (hb2 : b < t2) (hc1 : c < t1) :
    a ∈ aSlice b c ↔ a ≤ t := by
  have hz0 := z0_eq_of_t1_le_b_lt_t2 (a := a) (b := b) hb1 hb2
  have hc1R : (c : ℝ) < t1 := hc1
  change ((c : ℝ) < z0 a b) ↔ a ≤ t
  rw [hz0]
  constructor
  · intro hca
    by_contra hat
    have ht' : (t : ℝ) < a := lt_of_not_ge hat
    have ha1 : ¬ (a : ℝ) < t1 := not_lt_of_ge (le_trans t1_le_t2 (le_trans t2_le_t ht'.le))
    have hab : ¬ (a : ℝ) ≤ b := not_le_of_gt (lt_of_le_of_lt (le_trans hb2.le t2_le_t) ht')
    have ha2 : ¬ (a : ℝ) < t2 := not_lt_of_ge (le_trans t2_le_t ht'.le)
    have hat' : ¬ (a : ℝ) ≤ t := not_le_of_gt ht'
    have : (c : ℝ) < 0 := by simpa [ha1, hab, ha2, hat'] using hca
    exact (not_lt_of_ge (show (0 : ℝ) ≤ c from c.property.1) this)
  · intro hat
    have hz0_ge : (t1 : ℝ) ≤ z0 a b := by
      rw [hz0]
      by_cases ha1 : (a : ℝ) < t1
      · simp [ha1, le_trans t1_le_t2 t2_le_t]
      · by_cases hab : (a : ℝ) ≤ b
        · simpa [ha1, hab] using (t1_le_t2 : (t1 : ℝ) ≤ t2)
        · by_cases ha2 : (a : ℝ) < t2
          · simpa [ha1, hab, ha2] using hb1
          · have hat' : (a : ℝ) ≤ t := hat
            simp [ha1, hab, ha2, hat']
    exact lt_of_lt_of_le hc1R (by simpa [hz0] using hz0_ge)

private lemma mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_b {a b c : Rand}
    (hb1 : t1 ≤ b) (hb2 : b < t2) (hc1 : ¬ c < t1) (hcb : c < b) :
    a ∈ aSlice b c ↔ a < t2 := by
  have hz0 := z0_eq_of_t1_le_b_lt_t2 (a := a) (b := b) hb1 hb2
  have hcbR : (c : ℝ) < b := hcb
  change ((c : ℝ) < z0 a b) ↔ (a : ℝ) < t2
  rw [hz0]
  by_cases ha2 : (a : ℝ) < t2
  · by_cases ha1 : (a : ℝ) < t1
    · have : (c : ℝ) < t := lt_trans hcbR (lt_trans hb2 t2_lt_t)
      simpa [ha1, ha2] using this
    · by_cases hab : (a : ℝ) ≤ b
      · have : (c : ℝ) < t2 := lt_trans hcbR hb2
        simpa [ha1, hab, ha2] using this
      · simpa [ha1, hab, ha2] using hcbR
  · have ha2' : (t2 : ℝ) ≤ a := le_of_not_gt ha2
    have ha1 : ¬ (a : ℝ) < t1 := not_lt_of_ge (le_trans (t1_le_t2 : (t1 : ℝ) ≤ t2) ha2')
    have hab' : ¬ (a : ℝ) ≤ b := not_le_of_gt (lt_of_lt_of_le hb2 ha2')
    have hcge : (t1 : ℝ) ≤ c := le_of_not_gt hc1
    by_cases hat : (a : ℝ) ≤ t
    · have hct1 : ¬ (c : ℝ) < t1 := not_lt_of_ge hcge
      simp [ha2, ha1, hab', hat, hct1]
    · have hc0 : ¬ (c : ℝ) < 0 := not_lt_of_ge c.property.1
      simp [ha2, ha1, hab', hat, hc0]

private lemma mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_t2 {a b c : Rand}
    (hb1 : t1 ≤ b) (hb2 : b < t2) (hcb : ¬ c < b) (hc2 : c < t2) :
    a ∈ aSlice b c ↔ a ≤ b := by
  have hz0 := z0_eq_of_t1_le_b_lt_t2 (a := a) (b := b) hb1 hb2
  have hc2R : (c : ℝ) < t2 := hc2
  change ((c : ℝ) < z0 a b) ↔ a ≤ b
  rw [hz0]
  by_cases hab : (a : ℝ) ≤ b
  · by_cases ha1 : (a : ℝ) < t1
    · have hct : (c : ℝ) < t := lt_trans hc2R t2_lt_t
      refine ⟨fun _ => hab, fun _ => ?_⟩
      simpa [ha1, hab] using hct
    · refine ⟨fun _ => hab, fun _ => ?_⟩
      simpa [ha1, hab] using hc2R
  · have hab' : (b : ℝ) < a := lt_of_not_ge hab
    have ha1 : ¬ (a : ℝ) < t1 := not_lt_of_ge (le_trans hb1 hab'.le)
    have hnot : ¬ (c : ℝ) < z0 a b := by
      rw [hz0]
      by_cases ha2 : (a : ℝ) < t2
      · have hcbR : ¬ (c : ℝ) < b := by simpa using hcb
        simp [ha1, hab, ha2, hcbR]
      · have hbc : (b : ℝ) ≤ c := le_of_not_gt hcb
        have hcge : (t1 : ℝ) ≤ c := le_trans hb1 hbc
        by_cases hat : (a : ℝ) ≤ t
        · have hct1 : ¬ (c : ℝ) < t1 := not_lt_of_ge hcge
          simp [ha1, hab, ha2, hat, hct1]
        · have hc0 : ¬ (c : ℝ) < 0 := not_lt_of_ge c.property.1
          simp [ha1, hab, ha2, hat, hc0]
    have hnot' :
        ¬ (c : ℝ) <
            (if (a : ℝ) < t1 then (t : ℝ)
              else if (a : ℝ) ≤ b then (t2 : ℝ)
              else if (a : ℝ) < t2 then (b : ℝ)
              else if (a : ℝ) ≤ t then (t1 : ℝ)
              else 0) := by
      simpa [hz0] using hnot
    have hnot'' :
        ¬ (c : ℝ) <
            (if (a : ℝ) < t1 then (t : ℝ)
              else if (a : ℝ) < t2 then (b : ℝ)
              else if (a : ℝ) ≤ t then (t1 : ℝ)
              else 0) := by
      simpa [hab] using hnot'
    refine ⟨?_, ?_⟩
    · intro hlt
      have hlt' :
          (c : ℝ) <
            (if (a : ℝ) < t1 then (t : ℝ)
              else if (a : ℝ) < t2 then (b : ℝ)
              else if (a : ℝ) ≤ t then (t1 : ℝ)
              else 0) := by
        simpa [hab] using hlt
      exact False.elim (hnot'' hlt')
    · intro hab''
      exact False.elim (hab hab'')

private lemma mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_t {a b c : Rand}
    (hb1 : t1 ≤ b) (hb2 : b < t2) (hc2 : ¬ c < t2) (hct : c < t) :
    a ∈ aSlice b c ↔ a < t1 := by
  have hz0 := z0_eq_of_t1_le_b_lt_t2 (a := a) (b := b) hb1 hb2
  have hctR : (c : ℝ) < t := hct
  change ((c : ℝ) < z0 a b) ↔ (a : ℝ) < t1
  rw [hz0]
  by_cases ha1 : (a : ℝ) < t1
  · simpa [ha1] using hctR
  · have hcge : (t2 : ℝ) ≤ c := le_of_not_gt hc2
    have hz0_le : z0 a b ≤ t2 := by
      rw [hz0]
      by_cases hab : (a : ℝ) ≤ b
      · simp [ha1, hab]
      · by_cases ha2 : (a : ℝ) < t2
        · have hb_le : (b : ℝ) ≤ t2 := hb2.le
          simp [ha1, hab, ha2, hb_le]
        · by_cases hat : (a : ℝ) ≤ t
          · simpa [ha1, hab, ha2, hat] using (t1_le_t2 : (t1 : ℝ) ≤ t2)
          · have h0 : (0 : ℝ) ≤ t2 := t2.property.1
            simp [ha1, hab, ha2, hat, h0]
    have hle : z0 a b ≤ c := le_trans hz0_le hcge
    have hle' :
        (if (a : ℝ) < t1 then (t : ℝ)
          else if (a : ℝ) ≤ b then (t2 : ℝ)
          else if (a : ℝ) < t2 then (b : ℝ)
          else if (a : ℝ) ≤ t then (t1 : ℝ)
          else 0) ≤ c := by
      simpa [hz0] using hle
    refine ⟨?_, ?_⟩
    · intro hlt
      exact False.elim ((not_lt_of_ge hle') hlt)
    · intro hat1
      exact (ha1 hat1).elim

private lemma mem_aSlice_of_t1_le_b_lt_t2_of_not_c_lt_t {a b c : Rand}
    (hb1 : t1 ≤ b) (hb2 : b < t2) (hct : ¬ c < t) :
    a ∈ aSlice b c ↔ False := by
  have hz0 := z0_eq_of_t1_le_b_lt_t2 (a := a) (b := b) hb1 hb2
  change ((c : ℝ) < z0 a b) ↔ False
  constructor
  · intro hca
    have hz0_le : z0 a b ≤ t := by
      rw [hz0]
      by_cases ha1 : (a : ℝ) < t1
      · simp [ha1]
      · by_cases hab : (a : ℝ) ≤ b
        · simpa [ha1, hab] using (t2_le_t : (t2 : ℝ) ≤ t)
        · by_cases ha2 : (a : ℝ) < t2
          · have hb_le : (b : ℝ) ≤ t := le_trans hb2.le (t2_le_t : (t2 : ℝ) ≤ t)
            simp [ha1, hab, ha2, hb_le]
          · by_cases hat : (a : ℝ) ≤ t
            · have ht1t : (t1 : ℝ) ≤ t := by
                exact le_trans (t1_le_t2 : (t1 : ℝ) ≤ t2) (t2_le_t : (t2 : ℝ) ≤ t)
              simp [ha1, hab, ha2, hat, ht1t]
            · have h0 : (0 : ℝ) ≤ t := t.property.1
              simp [ha1, hab, ha2, hat, h0]
    have : (c : ℝ) < t := lt_of_lt_of_le hca hz0_le
    exact hct (show c < t from this)
  · intro hf
    exact False.elim hf

lemma aSlice_eq_of_t1_le_b_lt_t2 {b c : Rand} (hb1 : t1 ≤ b) (hb2 : b < t2) :
    aSlice b c =
      if c < t1 then Set.Iic t
      else if c < b then Set.Iio t2
      else if c < t2 then Set.Iic b
      else if c < t then Set.Iio t1
      else ∅ := by
  classical
  ext a
  by_cases hc1 : c < t1
  · rw [mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_t1 (a := a) hb1 hb2 hc1]
    simp [hc1]
  · by_cases hcb : c < b
    · rw [mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_b (a := a) hb1 hb2 hc1 hcb]
      simp [hc1, hcb]
    · by_cases hc2 : c < t2
      · rw [mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_t2 (a := a) hb1 hb2 hcb hc2]
        simp [hc1, hcb, hc2]
      · by_cases hct : c < t
        · rw [mem_aSlice_of_t1_le_b_lt_t2_of_c_lt_t (a := a) hb1 hb2 hc2 hct]
          simp [hc1, hcb, hc2, hct]
        · rw [mem_aSlice_of_t1_le_b_lt_t2_of_not_c_lt_t (a := a) hb1 hb2 hct]
          simp [hc1, hcb, hc2, hct]

/-!
## Computing `p`

We now compute the exact value of `ClassicalAlgorithm.p recursive3ParamAlg` by evaluating the
iterated `lintegral` from `p_eq_lintegral_innerBC`.
-/

open scoped Real Interval

namespace RealHelpers

/-- Shared skeleton: for a continuous, a.e.-nonnegative `f` on `Icc a b` whose interval integral
equals `v`, the `lintegral` of `ofReal ∘ f` is `ofReal v`. -/
private lemma lintegral_ofReal_of_integral_eq {f : ℝ → ℝ} {a b v : ℝ} (hab : a ≤ b)
    (hcont : Continuous f) (hnn : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    (hint : (∫ x in a..b, f x) = v) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal (f x) ∂(volume : Measure ℝ)) = ENNReal.ofReal v := by
  have hintOn : IntegrableOn f (Set.Icc a b) (volume : Measure ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := (volume : Measure ℝ)) hab).1
      (hcont.intervalIntegrable a b)
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Icc a b)] f :=
    MeasureTheory.ae_restrict_of_forall_mem (by measurability) hnn
  have hlin :
      (∫⁻ x in Set.Icc a b, ENNReal.ofReal (f x) ∂(volume : Measure ℝ)) =
        ENNReal.ofReal (∫ x in Set.Icc a b, f x ∂(volume : Measure ℝ)) := by
    simpa using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := (volume : Measure ℝ).restrict (Set.Icc a b)) (f := f) hintOn hnonneg).symm
  have hIcc : (∫ x in Set.Icc a b, f x ∂(volume : Measure ℝ)) = v := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hint]
  rw [hlin, hIcc]

lemma lintegral_ofReal_id_Icc (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal x ∂(volume : Measure ℝ)) =
      ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) :=
  lintegral_ofReal_of_integral_eq hab continuous_id (fun _ hx => le_trans ha hx.1) (by simp)

lemma lintegral_ofReal_sub_id_Icc (r a b : ℝ) (hbr : b ≤ r) (hab : a ≤ b) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal (r - x) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal (r * (b - a) - (b ^ 2 - a ^ 2) / 2) :=
  lintegral_ofReal_of_integral_eq hab (by continuity)
    (fun _ hx => sub_nonneg.2 (le_trans hx.2 hbr)) <| by
      have hconst : IntervalIntegrable (fun _x : ℝ => (r : ℝ)) (volume : Measure ℝ) a b :=
        intervalIntegral.intervalIntegrable_const
      have hid : IntervalIntegrable (fun x : ℝ => x) (volume : Measure ℝ) a b :=
        continuous_id.intervalIntegrable a b
      rw [intervalIntegral.integral_sub hconst hid]
      simp [intervalIntegral.integral_const]
      ring

lemma lintegral_ofReal_mul_sub_Icc (r a b : ℝ) (ha : 0 ≤ a) (hbr : b ≤ r) (hab : a ≤ b) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal (x * (r - x)) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal (r * (b ^ 2 - a ^ 2) / 2 - (b ^ 3 - a ^ 3) / 3) :=
  lintegral_ofReal_of_integral_eq hab (by continuity)
    (fun _ hx => mul_nonneg (le_trans ha hx.1) (sub_nonneg.2 (le_trans hx.2 hbr))) <| by
      have hpoly : (fun x : ℝ => x * (r - x)) = fun x : ℝ => r * x - x ^ (2 : ℕ) := by
        funext x; ring
      have hmul : IntervalIntegrable (fun x : ℝ => r * x) (volume : Measure ℝ) a b :=
        (continuous_const.mul continuous_id).intervalIntegrable a b
      have hsq : IntervalIntegrable (fun x : ℝ => x ^ (2 : ℕ)) (volume : Measure ℝ) a b :=
        (continuous_id.pow 2).intervalIntegrable a b
      rw [hpoly, intervalIntegral.integral_sub hmul hsq,
        intervalIntegral.integral_const_mul]
      simp
      ring

lemma lintegral_ofReal_pow_Icc (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal (x ^ n) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal ((b ^ (n + 1) - a ^ (n + 1)) / (n + 1)) :=
  lintegral_ofReal_of_integral_eq hab (continuous_id.pow n)
    (fun _ hx => pow_nonneg (le_trans ha hx.1) _) (by simp)

end RealHelpers

/-- The image of `Icc a b ⊆ Rand` under the coercion is the real interval `Icc a b`. -/
private lemma image_val_Icc (a b : Rand) :
    (Subtype.val '' Set.Icc a b : Set ℝ) = Set.Icc (a : ℝ) (b : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨y, ⟨le_trans a.property.1 hy.1, le_trans hy.2 b.property.2⟩⟩, hy, rfl⟩

/-- For `b ∈ Rand`, the order ideal `Iic b` is the closed interval `Icc 0 b`. -/
private lemma Iic_eq_Icc_zero (b : Rand) : (Set.Iic b : Set Rand) = Set.Icc (0 : Rand) b := by
  ext x
  simp [Set.mem_Iic, Set.mem_Icc]

/-- Lift a real `lintegral` over `Icc (a:ℝ) (b:ℝ)` to one over `Icc a b ⊆ Rand`. -/
private lemma setLIntegral_ofReal_lift (a b : Rand) (g : ℝ → ℝ) (v : ℝ)
    (hreal : (∫⁻ y in Set.Icc (a : ℝ) (b : ℝ), ENNReal.ofReal (g y) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal v) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal (g (x : ℝ)) ∂(volume : Measure Rand)) =
      ENNReal.ofReal v := by
  classical
  rw [unitInterval.volume_def]
  have hs : MeasurableSet (Set.Icc (0 : ℝ) 1) := by measurability
  have hsub :
      (∫⁻ x in Set.Icc a b, ENNReal.ofReal (g (x : ℝ)) ∂
          (Measure.comap (↑) (volume : Measure ℝ))) =
        ∫⁻ y in (Subtype.val '' Set.Icc a b), ENNReal.ofReal (g y) ∂(volume : Measure ℝ) := by
    simpa using
      (MeasureTheory.setLIntegral_subtype (μ := (volume : Measure ℝ))
        (s := Set.Icc (0 : ℝ) 1) hs (t := Set.Icc a b) (f := fun y : ℝ => ENNReal.ofReal (g y)))
  rwa [hsub, image_val_Icc]

lemma setLIntegral_ofReal_id_Icc (a b : Rand) (hab : a ≤ b) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal (x : ℝ) ∂(volume : Measure Rand)) =
      ENNReal.ofReal (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2) :=
  setLIntegral_ofReal_lift a b (fun y => y) _
    (RealHelpers.lintegral_ofReal_id_Icc (a := (a : ℝ)) (b := (b : ℝ)) a.property.1 hab)

/-- Lift an `Icc`-stated lintegral equality to an `Iio` one (the endpoint set is null). -/
private lemma setLIntegral_Iio_of_Icc (b : Rand) (h : Rand → ℝ≥0∞) (v : ℝ≥0∞)
    (hIcc : (∫⁻ x in Set.Icc (0 : Rand) b, h x ∂(volume : Measure Rand)) = v) :
    (∫⁻ x in Set.Iio b, h x ∂(volume : Measure Rand)) = v := by
  have hIio : (Set.Iio b : Set Rand) =ᵐ[(volume : Measure Rand)] Set.Iic b := by
    simpa using (MeasureTheory.Iio_ae_eq_Iic (μ := (volume : Measure Rand)) (a := b))
  rw [MeasureTheory.setLIntegral_congr (μ := (volume : Measure Rand)) hIio,
    Iic_eq_Icc_zero b, hIcc]

/-- Lift an `Icc`-stated lintegral equality to an `Ico` one (the endpoint set is null). -/
private lemma setLIntegral_Ico_of_Icc (a b : Rand) (h : Rand → ℝ≥0∞) (v : ℝ≥0∞)
    (hIcc : (∫⁻ x in Set.Icc a b, h x ∂(volume : Measure Rand)) = v) :
    (∫⁻ x in Set.Ico a b, h x ∂(volume : Measure Rand)) = v := by
  have hIco : (Set.Ico a b : Set Rand) =ᵐ[(volume : Measure Rand)] Set.Icc a b := by
    simpa using (MeasureTheory.Ico_ae_eq_Icc (μ := (volume : Measure Rand)) (a := a) (b := b))
  rw [MeasureTheory.setLIntegral_congr (μ := (volume : Measure Rand)) hIco, hIcc]

lemma setLIntegral_ofReal_id_Iio (b : Rand) :
    (∫⁻ x in Set.Iio b, ENNReal.ofReal (x : ℝ) ∂(volume : Measure Rand)) =
      ENNReal.ofReal (((b : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2) :=
  setLIntegral_Iio_of_Icc b _ _
    (by simpa using setLIntegral_ofReal_id_Icc (a := (0 : Rand)) (b := b) b.property.1)

lemma setLIntegral_ofReal_id_Ico (a b : Rand) (hab : a ≤ b) :
    (∫⁻ x in Set.Ico a b, ENNReal.ofReal (x : ℝ) ∂(volume : Measure Rand)) =
      ENNReal.ofReal (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2) :=
  setLIntegral_Ico_of_Icc a b _ _ (setLIntegral_ofReal_id_Icc a b hab)

lemma setLIntegral_ofReal_pow_Icc (n : ℕ) (a b : Rand) (hab : a ≤ b) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal ((x : ℝ) ^ n) ∂(volume : Measure Rand)) =
      ENNReal.ofReal (((b : ℝ) ^ (n + 1) - (a : ℝ) ^ (n + 1)) / (n + 1)) :=
  setLIntegral_ofReal_lift a b (fun y => y ^ n) _
    (RealHelpers.lintegral_ofReal_pow_Icc n (a := (a : ℝ)) (b := (b : ℝ)) a.property.1 hab)

open scoped Real Interval

lemma setLIntegral_ofReal_sub_id_Icc (r a b : Rand) (hab : a ≤ b) (hbr : (b : ℝ) ≤ (r : ℝ)) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal ((r : ℝ) - x) ∂(volume : Measure Rand)) =
      ENNReal.ofReal
        ((r : ℝ) * ((b : ℝ) - (a : ℝ)) - (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2)) :=
  setLIntegral_ofReal_lift a b (fun y => (r : ℝ) - y) _
    (RealHelpers.lintegral_ofReal_sub_id_Icc (r := (r : ℝ)) (a := (a : ℝ)) (b := (b : ℝ)) hbr hab)

lemma setLIntegral_ofReal_mul_sub_Icc (r a b : Rand) (hab : a ≤ b) (hbr : (b : ℝ) ≤ (r : ℝ)) :
    (∫⁻ x in Set.Icc a b, ENNReal.ofReal ((x : ℝ) * ((r : ℝ) - x)) ∂(volume : Measure Rand)) =
      ENNReal.ofReal
        ((r : ℝ) * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2 - (((b : ℝ) ^ 3 - (a : ℝ) ^ 3) / 3)) :=
  setLIntegral_ofReal_lift a b (fun y => y * ((r : ℝ) - y)) _
    (RealHelpers.lintegral_ofReal_mul_sub_Icc (r := (r : ℝ)) (a := (a : ℝ)) (b := (b : ℝ))
      a.property.1 hbr hab)

lemma setLIntegral_ofReal_sub_id_Ico (r a b : Rand) (hab : a ≤ b) (hbr : (b : ℝ) ≤ (r : ℝ)) :
    (∫⁻ x in Set.Ico a b, ENNReal.ofReal ((r : ℝ) - x) ∂(volume : Measure Rand)) =
      ENNReal.ofReal
        ((r : ℝ) * ((b : ℝ) - (a : ℝ)) - (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2)) :=
  setLIntegral_Ico_of_Icc a b _ _ (setLIntegral_ofReal_sub_id_Icc r a b hab hbr)

lemma setLIntegral_ofReal_mul_sub_Ico (r a b : Rand) (hab : a ≤ b) (hbr : (b : ℝ) ≤ (r : ℝ)) :
    (∫⁻ x in Set.Ico a b, ENNReal.ofReal ((x : ℝ) * ((r : ℝ) - x)) ∂(volume : Measure Rand)) =
      ENNReal.ofReal
        ((r : ℝ) * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2 - (((b : ℝ) ^ 3 - (a : ℝ) ^ 3) / 3)) :=
  setLIntegral_Ico_of_Icc a b _ _ (setLIntegral_ofReal_mul_sub_Icc r a b hab hbr)

lemma setLIntegral_ofReal_sub_id_Iio (r b : Rand) (hbr : (b : ℝ) ≤ (r : ℝ)) :
    (∫⁻ x in Set.Iio b, ENNReal.ofReal ((r : ℝ) - x) ∂(volume : Measure Rand)) =
      ENNReal.ofReal
        ((r : ℝ) * ((b : ℝ) - (0 : ℝ)) - (((b : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2)) :=
  setLIntegral_Iio_of_Icc b _ _
    (by simpa using setLIntegral_ofReal_sub_id_Icc r (0 : Rand) b b.property.1 hbr)

lemma setLIntegral_ofReal_mul_sub_Iio (r b : Rand) (hbr : (b : ℝ) ≤ (r : ℝ)) :
    (∫⁻ x in Set.Iio b, ENNReal.ofReal ((x : ℝ) * ((r : ℝ) - x)) ∂(volume : Measure Rand)) =
      ENNReal.ofReal
        ((r : ℝ) * ((b : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2 - (((b : ℝ) ^ 3 - (0 : ℝ) ^ 3) / 3)) :=
  setLIntegral_Iio_of_Icc b _ _
    (by simpa using setLIntegral_ofReal_mul_sub_Icc r (0 : Rand) b b.property.1 hbr)

end Recursive3Param
end UpperBound

end Distributed2Coloring
