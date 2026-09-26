/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.EMetricSpace.Basic


/-!
# Dyadic chaining on a bounded interval of nonnegative time

This file is deterministic infrastructure for a quantitative modulus of continuity.  It
subdivides the interval `[0, T]` of nonnegative real time into `2 ^ m` equal parts and records
what uniform control of the adjacent increments of a function `f : ℝ≥0 → E` on all subdivisions
from a base level downwards implies for pairs of subdivision points.

Main results:

* `MarkovProcess.dyadicTime`, the `i`-th point of the level-`m` subdivision of `[0, T]`, with its
  monotonicity, refinement and increment estimates;
* `MarkovProcess.HasDyadicAdjacentBound`, the hypothesis that all adjacent increments of `f` on
  the level-`m` subdivision are at most `e`;
* `MarkovProcess.edist_dyadicTime_le_of_hasDyadicAdjacentBound`, the same-level chaining bound;
* `MarkovProcess.edist_dyadicTime_ancestor_le`, the bound from a fine subdivision point to its
  canonical coarse ancestor by the sum of the intervening bounds;
* `MarkovProcess.edist_dyadicTime_le_of_sub_le`, the two-point chaining bound: subdivision points
  of level `n + r` whose indices differ by at most `2 ^ r` are within `2 * (chain sum) + e n`;
* `MarkovProcess.dyadicIndex` and its approximation lemmas, which locate an arbitrary time of
  `[0, T]` between consecutive subdivision points and compare the indices of two nearby times.

Everything here is a statement about a fixed function of time.  No measure, no probability law,
and no continuity of `f` is used or asserted.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess

section Subdivision

/-- The `i`-th point of the subdivision of `[0, T]` into `2 ^ m` equal parts. -/
noncomputable def dyadicTime (T : ℝ≥0) (m i : ℕ) : ℝ≥0 := T * i / 2 ^ m

theorem dyadicTime_coe (T : ℝ≥0) (m i : ℕ) :
    ((dyadicTime T m i : ℝ≥0) : ℝ) = (T : ℝ) * i / 2 ^ m := by
  simp [dyadicTime]

@[simp]
theorem dyadicTime_zero (T : ℝ≥0) (m : ℕ) : dyadicTime T m 0 = 0 := by
  simp [dyadicTime]

theorem dyadicTime_mono (T : ℝ≥0) (m : ℕ) {i j : ℕ} (hij : i ≤ j) :
    dyadicTime T m i ≤ dyadicTime T m j := by
  have hij' : (i : ℝ≥0) ≤ (j : ℝ≥0) := Nat.cast_le.mpr hij
  unfold dyadicTime
  gcongr

theorem dyadicTime_le (T : ℝ≥0) {m i : ℕ} (hi : i ≤ 2 ^ m) : dyadicTime T m i ≤ T := by
  rw [← NNReal.coe_le_coe, dyadicTime_coe, div_le_iff₀ (by positivity)]
  have hle : ((i : ℝ)) ≤ (2 : ℝ) ^ m := by exact_mod_cast hi
  exact mul_le_mul_of_nonneg_left hle T.coe_nonneg

/-- A subdivision point of level `m` is a subdivision point of level `m + 1`. -/
theorem dyadicTime_succ_level (T : ℝ≥0) (m i : ℕ) :
    dyadicTime T (m + 1) (2 * i) = dyadicTime T m i := by
  rw [← NNReal.coe_inj, dyadicTime_coe, dyadicTime_coe]
  push_cast
  rw [pow_succ]
  field_simp

theorem dist_dyadicTime (T : ℝ≥0) (m i j : ℕ) :
    dist (dyadicTime T m i) (dyadicTime T m j) = (T : ℝ) * |(i : ℝ) - j| / 2 ^ m := by
  rw [NNReal.dist_eq, dyadicTime_coe, dyadicTime_coe, div_sub_div_same, ← mul_sub, abs_div,
    abs_mul, abs_of_nonneg T.coe_nonneg, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m)]

theorem edist_dyadicTime_succ_le (T : ℝ≥0) (m i : ℕ) :
    edist (dyadicTime T m i) (dyadicTime T m (i + 1)) ≤ ((T / 2 ^ m : ℝ≥0) : ℝ≥0∞) := by
  rw [edist_dist]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [ENNReal.coe_toReal, dist_dyadicTime]
  push_cast
  rw [show (i : ℝ) - ((i : ℝ) + 1) = -1 by ring, abs_neg, abs_one, mul_one]

end Subdivision

section Chaining

variable {E : Type*} [PseudoEMetricSpace E]

/-- Every adjacent increment of `f` on the level-`m` subdivision of `[0, T]` is at most `e`. -/
def HasDyadicAdjacentBound (f : ℝ≥0 → E) (T : ℝ≥0) (m : ℕ) (e : ℝ≥0∞) : Prop :=
  ∀ i < 2 ^ m, edist (f (dyadicTime T m i)) (f (dyadicTime T m (i + 1))) ≤ e

/-- Same-level chaining: the increment between two subdivision points of the same level is at
most the number of intervening cells times the adjacent bound. -/
theorem edist_dyadicTime_le_of_hasDyadicAdjacentBound {f : ℝ≥0 → E} {T : ℝ≥0} {m : ℕ}
    {e : ℝ≥0∞} (hf : HasDyadicAdjacentBound f T m e) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ m) :
    edist (f (dyadicTime T m i)) (f (dyadicTime T m j)) ≤ (j - i : ℕ) * e := by
  have hchain := edist_le_Ico_sum_of_edist_le (f := fun k ↦ f (dyadicTime T m k)) hij
    (d := fun _ ↦ e) (fun {k} _ hkj ↦ hf k (lt_of_lt_of_le hkj hj))
  simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] using hchain

/-- Child-to-parent chaining: a level-`m + 1` subdivision point is within one adjacent bound of
the level-`m` point obtained by halving its index. -/
theorem edist_dyadicTime_parent_le {f : ℝ≥0 → E} {T : ℝ≥0} {m : ℕ} {e : ℝ≥0∞}
    (hf : HasDyadicAdjacentBound f T (m + 1) e) {i : ℕ} (hi : i ≤ 2 ^ (m + 1)) :
    edist (f (dyadicTime T (m + 1) i)) (f (dyadicTime T m (i / 2))) ≤ e := by
  rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
  · have hval : 2 * (i / 2) = i := by omega
    rw [← dyadicTime_succ_level T m (i / 2), hval, edist_self]
    exact zero_le
  · have hval : 2 * (i / 2) + 1 = i := by omega
    have hlt : 2 * (i / 2) < 2 ^ (m + 1) := by omega
    have hbound := hf (2 * (i / 2)) hlt
    rw [hval] at hbound
    rw [← dyadicTime_succ_level T m (i / 2), edist_comm]
    exact hbound

/-- Ancestor chaining: from a level-`n + r` subdivision point to the level-`n` point obtained by
dividing its index by `2 ^ r`, the increment is at most the sum of the intervening bounds. -/
theorem edist_dyadicTime_ancestor_le {f : ℝ≥0 → E} {T : ℝ≥0} {e : ℕ → ℝ≥0∞} {n : ℕ} :
    ∀ r : ℕ, (∀ k, n < k → k ≤ n + r → HasDyadicAdjacentBound f T k (e k)) →
      ∀ i ≤ 2 ^ (n + r),
        edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T n (i / 2 ^ r))) ≤
          ∑ s ∈ Finset.range r, e (n + s + 1) := by
  intro r
  induction r with
  | zero => intro _ i _; simp
  | succ r ihr =>
      intro hadj i hi
      have hlevel : n + (r + 1) = n + r + 1 := by omega
      have hi' : i ≤ 2 ^ (n + r + 1) := by rwa [← hlevel]
      have hparent : edist (f (dyadicTime T (n + r + 1) i))
          (f (dyadicTime T (n + r) (i / 2))) ≤ e (n + r + 1) :=
        edist_dyadicTime_parent_le (hadj (n + r + 1) (by omega) (by omega)) hi'
      have hpow : 2 ^ (n + r + 1) = 2 ^ (n + r) * 2 := by ring
      have hhalf : i / 2 ≤ 2 ^ (n + r) := by omega
      have hrest := ihr (fun k hk hk' ↦ hadj k hk (by omega)) (i / 2) hhalf
      have hdiv : i / 2 / 2 ^ r = i / 2 ^ (r + 1) := by
        rw [Nat.div_div_eq_div_mul]
        congr 1
        ring
      rw [hdiv] at hrest
      have htri : edist (f (dyadicTime T (n + (r + 1)) i))
            (f (dyadicTime T n (i / 2 ^ (r + 1)))) ≤
          edist (f (dyadicTime T (n + r + 1) i)) (f (dyadicTime T (n + r) (i / 2))) +
            edist (f (dyadicTime T (n + r) (i / 2))) (f (dyadicTime T n (i / 2 ^ (r + 1)))) := by
        rw [hlevel]
        exact edist_triangle _ _ _
      refine htri.trans ((add_le_add hparent hrest).trans_eq ?_)
      rw [Finset.sum_range_succ]
      exact add_comm _ _

/-- Two-point chaining: subdivision points of level `n + r` whose indices differ by at most
`2 ^ r` have a common level-`n` ancestor cell, so their increment is bounded by twice the chain
sum plus one coarse adjacent bound. -/
theorem edist_dyadicTime_le_of_sub_le {f : ℝ≥0 → E} {T : ℝ≥0} {e : ℕ → ℝ≥0∞} {n r : ℕ}
    (hadj : ∀ k, n ≤ k → k ≤ n + r → HasDyadicAdjacentBound f T k (e k))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ (n + r)) (hsub : j - i ≤ 2 ^ r) :
    edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T (n + r) j)) ≤
      2 * (∑ s ∈ Finset.range r, e (n + s + 1)) + e n := by
  have hi : i ≤ 2 ^ (n + r) := hij.trans hj
  have hanc := fun (k : ℕ) (hk : n < k) (hk' : k ≤ n + r) ↦ hadj k hk.le hk'
  have hleft := edist_dyadicTime_ancestor_le (f := f) (T := T) (e := e) (n := n) r hanc i hi
  have hright := edist_dyadicTime_ancestor_le (f := f) (T := T) (e := e) (n := n) r hanc j hj
  have hdivmono : i / 2 ^ r ≤ j / 2 ^ r := Nat.div_le_div_right hij
  have hdivclose : j / 2 ^ r ≤ i / 2 ^ r + 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by norm_num) r
    have hle : j ≤ i + 2 ^ r := by omega
    calc j / 2 ^ r ≤ (i + 2 ^ r) / 2 ^ r := Nat.div_le_div_right hle
      _ = i / 2 ^ r + 1 := by rw [Nat.add_div_right _ hpos]
  have hdivtop : j / 2 ^ r ≤ 2 ^ n := by
    calc j / 2 ^ r ≤ 2 ^ (n + r) / 2 ^ r := Nat.div_le_div_right hj
      _ = 2 ^ n := by rw [Nat.pow_div (by omega) (by norm_num), Nat.add_sub_cancel]
  have hmid : edist (f (dyadicTime T n (i / 2 ^ r))) (f (dyadicTime T n (j / 2 ^ r))) ≤ e n := by
    have hbase := edist_dyadicTime_le_of_hasDyadicAdjacentBound
      (hadj n le_rfl (Nat.le_add_right n r)) hdivmono hdivtop
    refine hbase.trans ?_
    have hcount : (j / 2 ^ r - i / 2 ^ r : ℕ) ≤ 1 := by omega
    calc ((j / 2 ^ r - i / 2 ^ r : ℕ) : ℝ≥0∞) * e n ≤ (1 : ℝ≥0∞) * e n := by
          gcongr
          exact_mod_cast hcount
      _ = e n := one_mul _
  have htri : edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T (n + r) j)) ≤
      edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T n (i / 2 ^ r))) +
        (edist (f (dyadicTime T n (i / 2 ^ r))) (f (dyadicTime T n (j / 2 ^ r))) +
          edist (f (dyadicTime T n (j / 2 ^ r))) (f (dyadicTime T (n + r) j))) :=
    (edist_triangle (f (dyadicTime T (n + r) i)) (f (dyadicTime T n (i / 2 ^ r)))
        (f (dyadicTime T (n + r) j))).trans
      (add_le_add le_rfl (edist_triangle (f (dyadicTime T n (i / 2 ^ r)))
        (f (dyadicTime T n (j / 2 ^ r))) (f (dyadicTime T (n + r) j))))
  refine htri.trans ?_
  rw [edist_comm (f (dyadicTime T n (j / 2 ^ r)))]
  have hsum := add_le_add hleft (add_le_add hmid hright)
  refine hsum.trans_eq ?_
  ring

end Chaining

section Approximation

/-- The index of the last level-`m` subdivision point of `[0, T]` at or below `s`. -/
noncomputable def dyadicIndex (T : ℝ≥0) (m : ℕ) (s : ℝ≥0) : ℕ := ⌊(s : ℝ) * 2 ^ m / T⌋₊

theorem dyadicIndex_le {T : ℝ≥0} (hT : 0 < T) {s : ℝ≥0} (hs : s ≤ T) (m : ℕ) :
    dyadicIndex T m s ≤ 2 ^ m := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hs' : (s : ℝ) ≤ (T : ℝ) := hs
  have hbound : (s : ℝ) * 2 ^ m / T ≤ ((2 ^ m : ℕ) : ℝ) := by
    rw [div_le_iff₀ hT']
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
  calc dyadicIndex T m s ≤ ⌊((2 ^ m : ℕ) : ℝ)⌋₊ := Nat.floor_mono hbound
    _ = 2 ^ m := Nat.floor_natCast _

theorem dyadicIndex_mono {T : ℝ≥0} (hT : 0 < T) (m : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    dyadicIndex T m s ≤ dyadicIndex T m t := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hst' : (s : ℝ) ≤ (t : ℝ) := hst
  exact Nat.floor_mono (by gcongr)

theorem dyadicTime_dyadicIndex_le {T : ℝ≥0} (hT : 0 < T) (m : ℕ) (s : ℝ≥0) :
    dyadicTime T m (dyadicIndex T m s) ≤ s := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hx0 : (0 : ℝ) ≤ (s : ℝ) * 2 ^ m / T := by positivity
  have hfloor : ((dyadicIndex T m s : ℕ) : ℝ) ≤ (s : ℝ) * 2 ^ m / T := Nat.floor_le hx0
  rw [← NNReal.coe_le_coe, dyadicTime_coe, div_le_iff₀ hpow]
  calc (T : ℝ) * ((dyadicIndex T m s : ℕ) : ℝ) ≤ (T : ℝ) * ((s : ℝ) * 2 ^ m / T) :=
        mul_le_mul_of_nonneg_left hfloor T.coe_nonneg
    _ = (s : ℝ) * 2 ^ m := by field_simp

theorem le_dyadicTime_dyadicIndex_add {T : ℝ≥0} (hT : 0 < T) (m : ℕ) (s : ℝ≥0) :
    s ≤ dyadicTime T m (dyadicIndex T m s) + T / 2 ^ m := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hfloor : (s : ℝ) * 2 ^ m / T < ((dyadicIndex T m s : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hlt : (s : ℝ) * 2 ^ m < (((dyadicIndex T m s : ℕ) : ℝ) + 1) * T :=
    (div_lt_iff₀ hT').mp hfloor
  rw [← NNReal.coe_le_coe]
  push_cast [dyadicTime_coe]
  rw [← add_div, le_div_iff₀ hpow]
  nlinarith [hlt]

theorem tendsto_dyadicTime_dyadicIndex {T : ℝ≥0} (hT : 0 < T) (s : ℝ≥0) :
    Tendsto (fun m ↦ dyadicTime T m (dyadicIndex T m s)) atTop (𝓝 s) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hzero : Tendsto (fun m : ℕ ↦ (T : ℝ) / 2 ^ m) atTop (𝓝 0) := by
    have hhalf : Tendsto (fun m : ℕ ↦ ((1 : ℝ) / 2) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul := hhalf.const_mul (T : ℝ)
    rw [mul_zero] at hmul
    refine hmul.congr fun m ↦ ?_
    rw [div_pow, one_pow]
    ring
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun m ↦ ?_) hzero
  have h1 : ((dyadicTime T m (dyadicIndex T m s) : ℝ≥0) : ℝ) ≤ (s : ℝ) :=
    dyadicTime_dyadicIndex_le hT m s
  have h2 : (s : ℝ) ≤ ((dyadicTime T m (dyadicIndex T m s) : ℝ≥0) : ℝ) + (T : ℝ) / 2 ^ m := by
    have h := NNReal.coe_le_coe.mpr (le_dyadicTime_dyadicIndex_add hT m s)
    push_cast at h
    exact h
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- Two nearby times of `[0, T]` have level-`n + r` subdivision indices that differ by at most
`2 ^ r`, once their separation is at most `T / 2 ^ (n + 1)` and `r` is at least one. -/
theorem dyadicIndex_sub_le {T : ℝ≥0} (hT : 0 < T) {s t : ℝ≥0} {n r : ℕ}
    (hr : 1 ≤ r) (hd : t ≤ s + T / 2 ^ (n + 1)) :
    dyadicIndex T (n + r) t - dyadicIndex T (n + r) s ≤ 2 ^ r := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hpow : (0 : ℝ) < 2 ^ (n + r) := by positivity
  set i : ℕ := dyadicIndex T (n + r) s with hi
  set j : ℕ := dyadicIndex T (n + r) t with hj
  have hjle : (j : ℝ) ≤ (t : ℝ) * 2 ^ (n + r) / T := Nat.floor_le (by positivity)
  have hilt : (s : ℝ) * 2 ^ (n + r) / T < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdreal : (t : ℝ) ≤ (s : ℝ) + (T : ℝ) / 2 ^ (n + 1) := by
    have := NNReal.coe_le_coe.mpr hd
    push_cast at this
    exact this
  have hsplit : (2 : ℝ) ^ (n + r) = 2 ^ (n + 1) * 2 ^ (r - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hstep : (t : ℝ) * 2 ^ (n + r) ≤
      (s : ℝ) * 2 ^ (n + r) + (2 : ℝ) ^ (r - 1) * T := by
    have hmul : (t : ℝ) * 2 ^ (n + r) ≤
        ((s : ℝ) + (T : ℝ) / 2 ^ (n + 1)) * 2 ^ (n + r) := by
      gcongr
    refine hmul.trans (le_of_eq ?_)
    rw [hsplit]
    field_simp
  have h1 : (j : ℝ) * T ≤ (t : ℝ) * 2 ^ (n + r) := by
    rwa [le_div_iff₀ hT'] at hjle
  have h2 : (s : ℝ) * 2 ^ (n + r) < ((i : ℝ) + 1) * T := (div_lt_iff₀ hT').mp hilt
  have h3 : (j : ℝ) * T < ((i : ℝ) + 1 + (2 : ℝ) ^ (r - 1)) * T := by
    have hexpand : ((i : ℝ) + 1 + (2 : ℝ) ^ (r - 1)) * T
        = ((i : ℝ) + 1) * T + (2 : ℝ) ^ (r - 1) * T := by ring
    rw [hexpand]
    linarith
  have hkey : (j : ℝ) < (i : ℝ) + 1 + (2 : ℝ) ^ (r - 1) :=
    lt_of_mul_lt_mul_right h3 hT'.le
  have hnat : j ≤ i + 2 ^ (r - 1) := by
    have hcast : (j : ℝ) < ((i + 2 ^ (r - 1) + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hcast)
  have hmono : 2 ^ (r - 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfinal : j - i ≤ 2 ^ (r - 1) := tsub_le_iff_right.mpr (by rw [add_comm]; exact hnat)
  exact hfinal.trans hmono

end Approximation

end MarkovProcess
