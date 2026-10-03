/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Data.Int.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Certified rational bounds for `log`, `arctan` and `sqrt`

Tools for the numerical verification of the potential inequality (6.2) (Lemma 6.1):

* `log_le_artanh` : upper bound for `log r`, `r ≥ 1`, by a partial sum of the artanh series plus
  an explicit geometric tail (complementing `log_ge_artanh`);
* `arctan_ge_partial` / `arctan_le_partial` : two-sided bounds for `arctan x`, `0 ≤ x < 1`, by
  partial sums of the alternating series;
* `arctan_eq_two_mul_arctan` : the half-angle reduction `arctan x = 2 arctan (x / (1 + √(1+x²)))`;
* `sqrt_le_of_sq_le`, `le_sqrt_of_sq_le` : rational enclosures of square roots.
-/

public section

open Finset Filter Topology

namespace Zeta5Irrational

/--
Upper bound for `log r`, `r ≥ 1`: partial sum plus the tail `2 z^(2m+1) / ((2m+1)(1 - z²))`. -/
lemma log_le_artanh {r : ℝ} (hr : 1 ≤ r) (m : ℕ) :
    Real.log r ≤
      2 * ∑ k ∈ range m, (1 / (2 * (k : ℝ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1) +
        2 * ((r - 1) / (r + 1)) ^ (2 * m + 1) / ((2 * m + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) := by
  set x : ℝ := (r - 1) / (r + 1) with hx
  have hr0 : 0 < r + 1 := by linarith
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hr0.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hr0]; linarith
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hr' : (1 + x) / (1 - x) = r := by rw [hx]; field_simp; ring
  have hlog : Real.log (1 + x) - Real.log (1 - x) = Real.log r := by
    rw [← Real.log_div (by linarith) (by linarith), hr']
  rw [hlog] at hsum
        -- split the series at `m`
  have hsplit := hsum.summable.sum_add_tsum_nat_add m
  rw [hsum.tsum_eq] at hsplit
        -- the tail is bounded by a geometric series
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hgeom :
    Summable fun k : ℕ => 2 * (1 / (2 * (m : ℝ) + 1)) * x ^ (2 * m + 1) * (x ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) hx2).mul_left _
  have htail :
    ∑' k : ℕ, 2 * (1 / (2 * ((k + m : ℕ) : ℝ) + 1)) * x ^ (2 * (k + m) + 1) ≤
      ∑' k : ℕ, 2 * (1 / (2 * (m : ℝ) + 1)) * x ^ (2 * m + 1) * (x ^ 2) ^ k := by
    refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff m).mpr hsum.summable) hgeom
    have hk : (1 / (2 * ((k + m : ℕ) : ℝ) + 1)) ≤ 1 / (2 * (m : ℝ) + 1) := by
      gcongr;
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hp : x ^ (2 * (k + m) + 1) = x ^ (2 * m + 1) * (x ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [hp]
    have : 0 ≤ x ^ (2 * m + 1) * (x ^ 2) ^ k := by positivity
    calc
      2 * (1 / (2 * ((k + m : ℕ) : ℝ) + 1)) * (x ^ (2 * m + 1) * (x ^ 2) ^ k) ≤
          2 * (1 / (2 * (m : ℝ) + 1)) * (x ^ (2 * m + 1) * (x ^ 2) ^ k) :=
        by gcongr
      _ = _ := by ring
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (by positivity) hx2] at htail
        -- assemble
  have hsum_eq :
    ∑ k ∈ range m, 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) =
      2 * ∑ k ∈ range m, (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) :=
    by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  rw [hsum_eq] at hsplit
  have h2 :
    2 * (1 / (2 * (m : ℝ) + 1)) * x ^ (2 * m + 1) * (1 - x ^ 2)⁻¹ =
      2 * x ^ (2 * m + 1) / ((2 * m + 1) * (1 - x ^ 2)) := by
    have : (1 : ℝ) - x ^ 2 ≠ 0 := by linarith
    field_simp
  rw [h2] at htail
  linarith

/-- Lower bound `arctan x ≥ ∑_{i < 2k} (-1)^i x^(2i+1)/(2i+1)` for `0 ≤ x < 1`. -/
lemma arctan_ge_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ≤ Real.arctan x := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  have hanti : Antitone fun i : ℕ => x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    intro i j hij
    have h1 : x ^ (2 * j + 1) ≤ x ^ (2 * i + 1) := pow_le_pow_of_le_one hx0 hx1.le (by omega)
    have h2 : (2 * (i : ℝ) + 1) ≤ 2 * (j : ℝ) + 1 := by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    exact div_le_div₀ (by positivity) h1 (by positivity) h2
  have htend := hs.tendsto_sum_nat
  have :=
    Antitone.alternating_series_le_tendsto (f := fun i : ℕ => x ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
      (by
        refine htend.congr fun n => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast; ring)
      hanti k
  exact this

/-- Upper bound `arctan x ≤ ∑_{i < 2k+1} (-1)^i x^(2i+1)/(2i+1)` for `0 ≤ x < 1`. -/
lemma arctan_le_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    Real.arctan x ≤
      ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  have hanti : Antitone fun i : ℕ => x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    intro i j hij
    have h1 : x ^ (2 * j + 1) ≤ x ^ (2 * i + 1) := pow_le_pow_of_le_one hx0 hx1.le (by omega)
    have h2 : (2 * (i : ℝ) + 1) ≤ 2 * (j : ℝ) + 1 := by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    exact div_le_div₀ (by positivity) h1 (by positivity) h2
  have htend := hs.tendsto_sum_nat
  exact
    Antitone.tendsto_le_alternating_series (f := fun i : ℕ => x ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
      (by
        refine htend.congr fun n => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast; ring)
      hanti k

/-- The half-angle reduction `arctan x = 2 arctan (x / (1 + √(1 + x²)))` for `x ≥ 0`. -/
lemma arctan_eq_two_mul_arctan {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x = 2 * Real.arctan (x / (1 + Real.sqrt (1 + x ^ 2))) := by
  set s := Real.sqrt (1 + x ^ 2) with hs
  have hs2 : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    rw [hs];
    exact Real.le_sqrt_of_sq_le (by nlinarith : (1 : ℝ) ^ 2 ≤ 1 + x ^ 2)
  set y := x / (1 + s) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by
    rw [hy, div_lt_one (by positivity)]
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
  have hyy : y * y < 1 := by nlinarith
  have hadd := Real.arctan_add (x := y) (y := y) (by nlinarith)
  have hval : (y + y) / (1 - y * y) = x := by
    rw [div_eq_iff (by nlinarith : (1 : ℝ) - y * y ≠ 0), hy]
    have h1s : (1 + s) ≠ 0 := by positivity
    field_simp
    nlinarith [hs2, hs1]
  rw [hval] at hadd
  linarith

/-- Rational enclosure of a square root: `√q ≤ u` if `q ≤ u²`, `0 ≤ u`. -/
lemma sqrt_le_of_sq_le {q u : ℝ} (hu : 0 ≤ u) (h : q ≤ u ^ 2) : Real.sqrt q ≤ u :=
  Real.sqrt_le_iff.mpr ⟨hu, h⟩

/-- Rational enclosure of a square root: `l ≤ √q` if `l² ≤ q`, `0 ≤ l`. -/
lemma le_sqrt_of_sq_le {q l : ℝ} (_hl : 0 ≤ l) (h : l ^ 2 ≤ q) : l ≤ Real.sqrt q :=
  Real.le_sqrt_of_sq_le h

end Zeta5Irrational
