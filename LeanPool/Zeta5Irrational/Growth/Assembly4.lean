/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.PrimeSumIntegral
public import LeanPool.Zeta5Irrational.Growth.TailIntegral
import LeanPool.Zeta5Irrational.Growth.TableIntegrals
public import LeanPool.Zeta5Irrational.Growth.OuterTable
import LeanPool.Zeta5Irrational.Growth.TableGen
import Mathlib.Tactic.ReduceModChar
public import LeanPool.Zeta5Irrational.Growth.Assembly3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Growth: the limits of the three prime sums
-/

public section

open Finset Filter

namespace Zeta5Irrational

lemma aIn_le : ∀ i < 125, |((aInL.getD i 0 : ℚ) : ℝ)| ≤ 100 := by
  intro i hi
  interval_cases i <;> simp only [aInL, List.getD_cons_succ, List.getD_cons_zero] <;>
    norm_num [abs_le]

lemma aOut_le : ∀ i < 13, |((aOutL.getD i 0 : ℚ) : ℝ)| ≤ 100 := by
  intro i hi
  interval_cases i <;> simp only [aOutL, List.getD_cons_succ, List.getD_cons_zero] <;>
    norm_num [abs_le]

lemma lin_lip (a b : ℝ) (L : ℝ) (ha : |a| ≤ L) (x y : ℝ) :
    |(a * x + b) - (a * y + b)| ≤ L * |x - y| := by
  rw [show (a * x + b) - (a * y + b) = a * (x - y) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)

/-- **The inner table sum.** -/
lemma inner_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop,
      psum fIn 3 20 K / K ^ 2 ≤ 322437603634266857629 / 7535670527041937280000 + δ := by
  have h :=
    psum_piecewise_le (f := fIn) (g := gIn) (t := tIn) (L := 100) 125 (by rw [tIn_zero]; norm_num)
      tIn_mono (by norm_num) (fun i _ => by unfold gIn; fun_prop)
      (fun i hi x _ y _ => by unfold gIn; exact lin_lip _ _ _ (aIn_le i hi) x y)
      (fun i hi x hx => by unfold fIn; rw [pieceIdx_eq tIn_mono hi hx]) hδ
  rw [tIn_zero, tIn_last, inner_integrals] at h
  exact h

lemma tOut_zero : tOut 0 = 20 / 37 := by simp [tOut, tOutL]

lemma tOut_last : tOut 13 = 3 := by simp [tOut, tOutL]

/-- **The outer table sum.** -/
lemma outer_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop, psum Eout (20 / 37) 3 K / K ^ 2 ≤ 129101 / 96000 + δ := by
  have h :=
    psum_piecewise_le (f := Eout) (g := gOut) (t := tOut) (L := 100) 13
      (by rw [tOut_zero]; norm_num) tOut_mono (by norm_num) (fun i _ => by unfold gOut; fun_prop)
      (fun i hi x _ y _ => by unfold gOut; exact lin_lip _ _ _ (aOut_le i hi) x y)
      (fun i hi x hx => outer_table i hi x hx) hδ
  rw [tOut_zero, tOut_last, outer_integrals] at h
  exact h

lemma tT_zero : tT 0 = 20 := by unfold tT; norm_num

lemma tT_last : tT 1140 = 400 := by unfold tT; norm_num

lemma qT_le_400 {i : ℕ} (hi : i < 1140) : (qT i : ℝ) ≤ 400 := by
  unfold qT;
  exact_mod_cast (show (60 + i) / 3 ≤ 400 by omega)

lemma qT'_le_30 {i : ℕ} (hi : i < 1140) : (qT' i : ℝ) ≤ 30 := by
  unfold qT';
  exact_mod_cast (show (60 + i) / 40 ≤ 30 by omega)

lemma tT_le_400 {i : ℕ} (hi : i ≤ 1140) : tT i ≤ 400 := by
  unfold tT; have : (i : ℝ) ≤ 1140 := by exact_mod_cast hi
  linarith

/-- **The tail sum.** -/
lemma tail_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop,
      psum (fun x => x * Ftail x + 27 / 16) 20 400 K / K ^ 2 ≤ -6843153 / 128000000 + δ := by
  have h :=
    psum_piecewise_le (f := fun x => x * Ftail x + 27 / 16) (g := gT) (t := tT) (L := 3000) 1140
      (by rw [tT_zero]; norm_num) (fun i _ => by rw [tT_succ]; linarith) (by norm_num)
      (fun i _ => (continuous_gT i).continuousOn)
      (fun i hi x hx y hy =>
        by
        have hx0 : 0 ≤ x := by linarith [hx.1, tT_pos i]
        have hy0 : 0 ≤ y := by linarith [hy.1, tT_pos i]
        have hx4 : x ≤ 400 := hx.2.trans (tT_le_400 (by omega))
        have hy4 : y ≤ 400 := hy.2.trans (tT_le_400 (by omega))
        have hq := qT_le_400 hi
        have hq' := qT'_le_30 hi
        have hq0 : (0 : ℝ) ≤ qT i := by positivity
        have hq0' : (0 : ℝ) ≤ qT' i := by positivity
        have e :
          gT i x - gT i y =
            (x - y) *
              (37 / 10 - 37 / 20 * (qT i : ℝ) + 111 / 10 * (qT' i : ℝ) + 407 / 400 * (x + y)) :=
          by unfold gT FT; ring
        rw [e, abs_mul, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [abs_le]; constructor <;> nlinarith)
      (fun i hi x hx => by
        obtain ⟨hx1, hx2⟩ := hx
        have h1 := qT_le i; have h2 := tT_succ_le i; have h3 := qT'_le i; have h4 := tT_succ_le' i
        have hf : Int.fract x = x - qT i := fract_of_bounds (by linarith) (by linarith)
        have hg : Int.fract (3 / 40 * x) = 3 / 40 * x - qT' i :=
          fract_of_bounds (by linarith) (by linarith)
        unfold gT FT Ftail
        rw [hf, hg]; ring)
      hδ
  have hsum := tail_sum_le
  rw [tT_zero, tT_last] at h
  filter_upwards [h] with K hK
  linarith

end Zeta5Irrational
