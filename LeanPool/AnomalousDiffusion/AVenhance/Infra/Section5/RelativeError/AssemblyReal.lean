/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # abstract real lemmas for the main-theorem assembly  Pure real-variable statements used by the
assembly: the telescoping lower bound `s_n ≥ (1 - ∑ e_i) s_j`, the geometric tail estimate, and the
passage from a lower bound along a sequence tending to `0⁺` to a lower bound for the `limsup`.
-/

@[expose] public section

open Filter Topology

namespace AVenhance.Infra.Section5.RelativeError

/-- Telescoping lower bound from `s_{i+1} ≥ (1 - e_i) s_i` for `j ≤ i < N`, with `0 ≤ e_i ≤ 1`
there: the product is bounded below by `1 - ∑ e_i`. -/
theorem telescope_lower {s e : ℕ → ℝ} {j N : ℕ} (hs : 0 ≤ s j)
    (he0 : ∀ i, j ≤ i → i < N → 0 ≤ e i) (he1 : ∀ i, j ≤ i → i < N → e i ≤ 1)
    (hstep : ∀ i, j ≤ i → i < N → (1 - e i) * s i ≤ s (i + 1)) (n : ℕ) (hn : j + n ≤ N) :
    (1 - ∑ i ∈ Finset.range n, e (j + i)) * s j ≤ s (j + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    have hS : 0 ≤ ∑ i ∈ Finset.range n, e (j + i) :=
      Finset.sum_nonneg fun i hi =>
        he0 _ (by omega) (by have := Finset.mem_range.1 hi; omega)
    have h1 : 0 ≤ 1 - e (j + n) := sub_nonneg.2 (he1 _ (by omega) (by omega))
    have h2 := hstep (j + n) (by omega) (by omega)
    have h3 := mul_le_mul_of_nonneg_left ih h1
    have h4 : 0 ≤ e (j + n) * (∑ i ∈ Finset.range n, e (j + i)) * s j :=
      mul_nonneg (mul_nonneg (he0 _ (by omega) (by omega)) hS) hs
    rw [Finset.sum_range_succ, show j + (n + 1) = j + n + 1 by ring]
    nlinarith only [h2, h3, h4]

/-- Geometric tail: `∑_{i<n} ρ^{j+i} ≤ ρ^j/(1-ρ)`. -/
theorem geom_tail_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (j n : ℕ) :
    ∑ i ∈ Finset.range n, ρ ^ (j + i) ≤ ρ ^ j / (1 - ρ) := by
  have h := geom_sum_Ico_le_of_lt_one (m := j) (n := j + n) h0 h1
  rwa [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at h

/-- Smallness of the weighted geometric tail starting at index `j ≥ 1`. -/
theorem weighted_geom_tail_le {C ρ : ℝ} (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hCρ : C * ρ ≤ 1 / 4) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    C * ∑ i ∈ Finset.range n, ρ ^ (j + i) ≤ 1 / 2 := by
  have hρ1 : ρ < 1 := by linarith
  have h1 := geom_tail_le hρ0 hρ1 j n
  have hpow : ρ ^ j ≤ ρ := by
    simpa using pow_le_pow_of_le_one hρ0 hρ1.le hj
  have hd : 0 < 1 - ρ := by linarith
  have h2 : ρ ^ j / (1 - ρ) ≤ 2 * ρ := by
    rw [div_le_iff₀ hd]
    nlinarith only [hpow, hρ0, hρ]
  calc C * ∑ i ∈ Finset.range n, ρ ^ (j + i) ≤ C * (2 * ρ) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hC
    _ = 2 * (C * ρ) := by ring
    _ ≤ 1 / 2 := by linarith

/-- If `x_m → 0` through positive reals and `e > 0` then `A x_m^e` is eventually below any
positive bound. -/
theorem eventually_mul_rpow_le {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 0)) {e : ℝ} (he : 0 < e)
    (A : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ m in atTop, A * x m ^ e ≤ δ := by
  have h1 : Tendsto (fun m => x m ^ e) atTop (𝓝 (0 ^ e)) :=
    hx.rpow_const (Or.inr he.le)
  rw [Real.zero_rpow he.ne'] at h1
  have h2 := h1.const_mul A
  rw [mul_zero] at h2
  exact (h2.eventually (gt_mem_nhds hδ)).mono fun m hm => hm.le

/-- A positive sequence tending to `0` has positive powers tending to `0⁺`. -/
theorem tendsto_rpow_nhdsGT {x : ℕ → ℝ} (hx0 : ∀ m, 0 < x m) (hx : Tendsto x atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) : Tendsto (fun m => x m ^ s) atTop (𝓝[>] 0) := by
  have h1 : Tendsto (fun m => x m ^ s) atTop (𝓝 (0 ^ s)) := hx.rpow_const (Or.inr hs.le)
  rw [Real.zero_rpow hs.ne'] at h1
  exact tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun m => Real.rpow_pos_of_pos (hx0 m) s⟩

/-- A lower bound along a sequence tending to `0⁺` passes to the `limsup` at `0⁺`, given an upper
bound for the function near `0⁺`. -/
theorem le_limsup_of_seq {F : ℝ → ℝ} {κ : ℕ → ℝ} (hκ : Tendsto κ atTop (𝓝[>] 0)) {B U : ℝ}
    (hU : ∀ᶠ k in 𝓝[>] (0 : ℝ), F k ≤ U) (hlow : ∀ᶠ m in atTop, B ≤ F (κ m)) :
    B ≤ limsup F (𝓝[>] (0 : ℝ)) :=
  le_limsup_of_frequently_le (hκ.frequently hlow.frequently) ⟨U, hU⟩

end AVenhance.Infra.Section5.RelativeError
