/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.TorusReduction
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Push

/-!
# Simultaneous Dirichlet approximation ⟹ `RecordsContinue` (makes `g_∞ ≤ 2^d+1` unconditional)

The higher-dimensional three-distance bound `g_∞ ≤ 2^d+1` (`DeltaCost`, `TorusReduction`) was proved
under the hypothesis `RecordsContinue (deltaCost α)` — the best simultaneous approximations of `α`
improve without bound. This file **discharges that hypothesis** from a clean, standard irrationality
condition (some coordinate `α k` is irrational), via the elementary **box pigeonhole** form of
Dirichlet's simultaneous approximation theorem — no homogeneous dynamics, no measure theory.

* **`exists_delta_lt`** (Dirichlet): for every `ε > 0` there is a denominator `q ≥ 1` with the
defect
  `delta α q < ε`. Proof: among the `Q^d + 1` points `{i • α mod ℤᵈ : 0 ≤ i ≤ Q^d}` two share one of
  the `Q^d` sub-boxes of side `1/Q` (`Fintype` pigeonhole); their index difference `q` has all
  coordinates within `1/Q` of an integer, so `delta α q < 1/Q ≤ ε`.
* **`delta_pos`**: `delta α q > 0` for `q ≥ 1` when some `α k` is irrational (`q α k ∉ ℤ`).
* **`recordsContinue_deltaCost`**: assembling the two — for every `q ≥ 1` there is `q' > q` with
  `delta α q' < delta α q`. (If not, `delta α` would be bounded below by a positive constant on all
  of `ℕ₊`, contradicting Dirichlet.) This is exactly `RecordsContinue (deltaCost α)`.

Hence the `L^∞` higher-dimensional three-distance theorem holds for every `α` with an irrational
coordinate, **with no remaining hypothesis** (`nnDist_count_unconditional`,
`nnDist_count_plane_unconditional`). Axiom-clean.
-/

namespace ThreeGap.SimDirichlet

open ThreeGap.SimApprox ThreeGap.Chevallier ThreeGap.DeltaCost

variable {d : ℕ}

/-! ## Dirichlet via the box pigeonhole -/

/-- The box index of the point `i • α` in direction `k`, at resolution `Q`: `⌊{i αₖ}·Q⌋ ∈
{0,…,Q−1}`,
packaged as `Fin Q`. -/
noncomputable def box (α : Fin d → ℝ) (Q : ℕ) (hQ : 1 ≤ Q) (i : ℕ) : Fin d → Fin Q :=
  fun k => ⟨(⌊Int.fract ((i : ℝ) * α k) * Q⌋).toNat, by
    have hfr : Int.fract ((i : ℝ) * α k) < 1 := Int.fract_lt_one _
    have hfr0 : 0 ≤ Int.fract ((i : ℝ) * α k) := Int.fract_nonneg _
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hlt : Int.fract ((i : ℝ) * α k) * Q < Q := by nlinarith
    have hub : ⌊Int.fract ((i : ℝ) * α k) * Q⌋ < (Q : ℤ) := by
      exact_mod_cast lt_of_le_of_lt (Int.floor_le _) hlt
    have hge : 0 ≤ ⌊Int.fract ((i : ℝ) * α k) * Q⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
    omega⟩

/-- **Dirichlet's simultaneous approximation theorem (inverse-resolution form).** For `Q ≥ 1` there
is
a denominator `1 ≤ q` with `delta α q < 1/Q`. -/
theorem exists_delta_lt_inv (α : Fin d → ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ delta α q < 1 / Q := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  -- pigeonhole: two of the Q^d + 1 points share a box
  have hcard : (Finset.univ : Finset (Fin d → Fin Q)).card < (Finset.range (Q ^ d + 1)).card := by
    rw [Finset.card_range, Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    exact Nat.lt_succ_self _
  obtain ⟨i₀, _, j₀, _, hij, hbox₀⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun a _ => Finset.mem_univ (box α Q hQ a))
  -- orient the pair so that `i < j`
  obtain ⟨i, j, hlt, hbox⟩ :
      ∃ i j, i < j ∧ box α Q hQ i = box α Q hQ j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i₀, j₀, h, hbox₀⟩
    · exact ⟨j₀, i₀, h, hbox₀.symm⟩
  -- the integer translate: M k = ⌊j αₖ⌋ − ⌊i αₖ⌋
  set q : ℕ := j - i with hq
  refine ⟨q, by omega, ?_⟩
  set M : Fin d → ℤ := fun k => ⌊(j : ℝ) * α k⌋ - ⌊(i : ℝ) * α k⌋ with hM
  -- each coordinate of the remainder is the fractional-part difference, hence `< 1/Q`
  have hcoord : ∀ k, |rem α (q : ℤ) M k| < 1 / Q := by
    intro k
    have hboxk : (box α Q hQ i k : ℕ) = (box α Q hQ j k : ℕ) := by rw [hbox]
    simp only [box] at hboxk
    have hfloor : ⌊Int.fract ((i : ℝ) * α k) * Q⌋ = ⌊Int.fract ((j : ℝ) * α k) * Q⌋ := by
      have hi0 : 0 ≤ ⌊Int.fract ((i : ℝ) * α k) * Q⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
      have hj0 : 0 ≤ ⌊Int.fract ((j : ℝ) * α k) * Q⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
      omega
    have habs : |Int.fract ((i : ℝ) * α k) * Q - Int.fract ((j : ℝ) * α k) * Q| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hfloor
    -- rem coordinate = fract(j αₖ) − fract(i αₖ)
    have hrem : rem α (q : ℤ) M k = Int.fract ((j : ℝ) * α k) - Int.fract ((i : ℝ) * α k) := by
      simp only [rem, hM, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.fract]
      rw [hq, Nat.cast_sub hlt.le]
      push_cast
      ring
    -- |fract(j) − fract(i)| = (1/Q)·|fract(i)·Q − fract(j)·Q| < 1/Q
    have heq : |Int.fract ((i : ℝ) * α k) * Q - Int.fract ((j : ℝ) * α k) * Q|
        = (Q : ℝ) * |Int.fract ((j : ℝ) * α k) - Int.fract ((i : ℝ) * α k)| := by
      rw [← sub_mul, abs_mul, abs_of_pos hQ0, abs_sub_comm, mul_comm]
    have hkey : (Q : ℝ) * |Int.fract ((j : ℝ) * α k) - Int.fract ((i : ℝ) * α k)| < 1 := heq ▸ habs
    rw [hrem, lt_div_iff₀ hQ0, mul_comm]
    exact hkey
  -- so `delta α q ≤ ‖rem α q M‖ < 1/Q`
  calc delta α (q : ℤ) ≤ ‖rem α (q : ℤ) M‖ := delta_le α (q : ℤ) M
    _ < 1 / Q := by
        rw [pi_norm_lt_iff (by positivity)]
        intro k
        rw [Real.norm_eq_abs]
        exact hcoord k

/-- **Dirichlet's theorem (ε form).** For every `ε > 0` there is `q ≥ 1` with `delta α q < ε`. -/
theorem exists_delta_lt (α : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ delta α q < ε := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / ε)
  have hQ1 : 1 ≤ Q := by
    by_contra h
    push Not at h
    interval_cases Q
    · simp only [Nat.cast_zero] at hQ; exact absurd hQ (not_lt.mpr (by positivity))
  obtain ⟨q, hq1, hq2⟩ := exists_delta_lt_inv α Q hQ1
  refine ⟨q, hq1, lt_of_lt_of_le hq2 ?_⟩
  rw [div_le_iff₀ (by exact_mod_cast hQ1 : (0:ℝ) < Q)]
  rw [div_lt_iff₀ hε] at hQ
  nlinarith [hQ]

/-! ## Positivity from irrationality -/

/-- If some coordinate `α k` is irrational, the defect is **strictly positive** at every `q ≥ 1`
(then `q αₖ ∉ ℤ`, so its distance to the nearest integer is positive). -/
theorem delta_pos (α : Fin d → ℝ) {k₀ : Fin d} (hirr : Irrational (α k₀)) {q : ℕ} (hq : 1 ≤ q) :
    0 < delta α q := by
  -- lower bound: delta α q ≥ |q αₖ₀ − round(q αₖ₀)|
  have hirrq : Irrational ((q : ℝ) * α k₀) := hirr.natCast_mul (by omega : q ≠ 0)
  have hne : (q : ℝ) * α k₀ - round ((q : ℝ) * α k₀) ≠ 0 := by
    intro h
    apply hirrq
    exact ⟨round ((q : ℝ) * α k₀), by push_cast; linarith [h]⟩
  have hposc : 0 < |(q : ℝ) * α k₀ - round ((q : ℝ) * α k₀)| := abs_pos.mpr hne
  refine lt_of_lt_of_le hposc ?_
  -- |q αₖ₀ − round| ≤ ‖rem α q p‖ for all p, hence ≤ delta (= inf)
  refine le_ciInf (fun p => ?_)
  calc |(q : ℝ) * α k₀ - round ((q : ℝ) * α k₀)|
      ≤ |(q : ℝ) * α k₀ - (p k₀ : ℝ)| := round_le _ _
    _ = ‖rem α (q : ℤ) p k₀‖ := by
        rw [Real.norm_eq_abs, rem]; simp [Pi.smul_apply, smul_eq_mul]
    _ ≤ ‖rem α (q : ℤ) p‖ := norm_le_pi_norm _ k₀

/-! ## Assembly: `RecordsContinue` -/

/-- **`RecordsContinue (deltaCost α)` from irrationality.** If some coordinate of `α` is irrational,
the best simultaneous approximations improve without bound: every `q ≥ 1` is beaten by a larger
denominator. (Else `delta α` would have a positive lower bound on all of `ℕ₊`, contradicting
Dirichlet.) -/
theorem recordsContinue_deltaCost (α : Fin d → ℝ) {k₀ : Fin d} (hirr : Irrational (α k₀)) :
    RecordsContinue (deltaCost α) := by
  intro q hq
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ q' > q, deltaCost α q ≤ deltaCost α q'
  -- the minimum of delta over {1,…,q} is positive
  set δ₀ : ℝ := (Finset.Icc 1 q).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hq⟩⟩ (deltaCost α) with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀, Finset.lt_inf'_iff]
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact delta_pos α hirr hj.1
  -- every denominator ≥ 1 has delta ≥ δ₀ — contradicting Dirichlet
  have hlb : ∀ q' : ℕ, 1 ≤ q' → δ₀ ≤ deltaCost α q' := by
    intro q' hq'
    rcases le_or_gt q' q with h | h
    · exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hq', h⟩)
    · calc δ₀ ≤ deltaCost α q := Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hq, le_refl q⟩)
        _ ≤ deltaCost α q' := hcon q' h
  obtain ⟨q', hq'1, hq'2⟩ := exists_delta_lt α hδ₀pos
  exact absurd (hlb q' hq'1) (not_le.mpr hq'2)

/-! ## Unconditional higher-dimensional three-distance bounds -/

/-- **`g_∞ ≤ 2^d + 1`, unconditional.** For any `α : Fin d → ℝ` with an irrational coordinate and
any
`N ≥ 2`, the orbit `{0, α, …, Nα}` on the torus `𝕋ᵈ` has at most `2^d + 1` distinct
nearest-neighbour
distances in the sup-norm metric. No `RecordsContinue` hypothesis — it is discharged from
irrationality via Dirichlet. -/
theorem nnDist_count_unconditional (α : Fin d → ℝ) {k₀ : Fin d} (hirr : Irrational (α k₀)) {N : ℕ}
    (hN : 2 ≤ N) : ((Finset.range (N + 1)).image (nnDist α N)).card ≤ 2 ^ d + 1 :=
  nnDist_count_le α (recordsContinue_deltaCost α hirr) hN

/-- **The `L^∞` five-distance theorem on `𝕋²`, unconditional.** For any `α : Fin 2 → ℝ` with an
irrational coordinate and any `N ≥ 2`, the orbit `{0, α, …, Nα}` on `𝕋²` has at most **five**
distinct
nearest-neighbour distances in the sup-norm metric. -/
theorem nnDist_count_plane_unconditional (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀))
    {N : ℕ} (hN : 2 ≤ N) : ((Finset.range (N + 1)).image (nnDist α N)).card ≤ 5 :=
  nnDist_count_le_plane α (recordsContinue_deltaCost α hirr) hN

end ThreeGap.SimDirichlet
