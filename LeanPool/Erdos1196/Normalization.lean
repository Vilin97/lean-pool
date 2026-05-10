/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import LeanPool.Erdos1196.NormalizationCore
import LeanPool.Erdos1196.NormalizationSmallPrime

/-!
# First-entry bounds for the normalization constant

This file completes the normalization decomposition by summing the first-entry rows and
proving the final estimate for the first-entry contribution to `B_x`.

## Main statements

* `normalizationFirstEntryPart_estimate`
-/

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/--
If every first-entry row is summable, then the corresponding contribution to `B_x` is exactly the
finite parent-state sum appearing in the first-entry decomposition.
-/
lemma hasSum_normalizationFirstEntryPart {x Y : ℕ} (hx : 1 ≤ x)
    (hsummable :
      ∀ {m : ℕ}, 1 ≤ m → m < x →
        Summable (fun q : ℕ =>
          if entryThreshold x Y m ≤ q then
            Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
          else 0)) :
    HasSum (fun n : ℕ => normalizationFirstEntryPart x Y n)
      (∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m) := by
  let row : ℕ → ℝ := fun m => ∑' q : ℕ, firstEntryPairWeight x Y (m, q)
  have hrow :
      ∀ m : ℕ,
        row m = if 1 ≤ m ∧ m < x then (1 / (m : ℝ)) * firstEntryTail x Y m else 0 := by
    intro m
    dsimp [row]
    rw [firstEntryPairWeight_row]
    by_cases hm : 1 ≤ m ∧ m < x
    · rw [if_pos hm, tsum_mul_left, firstEntryTail, if_pos hm]
    · simp [hm]
  have hslice :
      ∀ m : ℕ, Summable (fun q : ℕ => firstEntryPairWeight x Y (m, q)) := by
    intro m
    rw [firstEntryPairWeight_row]
    by_cases hm : 1 ≤ m ∧ m < x
    · rcases hm with ⟨hm1, hmx⟩
      rw [if_pos ⟨hm1, hmx⟩]
      exact (hsummable hm1 hmx).mul_left (1 / (m : ℝ))
    · simp [hm]
  have hIcc : ∀ m : ℕ, (1 ≤ m ∧ m < x) ↔ m ∈ Finset.Icc 1 (x - 1) := by
    intro m
    simp [Finset.mem_Icc]
    omega
  have hrow_zero : ∀ m ∉ Finset.Icc 1 (x - 1), row m = 0 := by
    intro m hm
    rw [hrow m, if_neg]
    simpa [hIcc m] using hm
  have hrow_summable : Summable row := by
    refine summable_of_hasFiniteSupport ((Finset.Icc 1 (x - 1)).finite_toSet.subset ?_)
    intro m hm
    by_contra hm'
    exact hm (hrow_zero m hm')
  have hpair_nonneg : ∀ p : ℕ × ℕ, 0 ≤ firstEntryPairWeight x Y p := by
    rintro ⟨m, q⟩
    by_cases hp : 1 ≤ m ∧ m < x ∧ entryThreshold x Y m ≤ q
    · rw [firstEntryPairWeight, if_pos hp]
      rw [Nat.cast_mul]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · simp [firstEntryPairWeight, hp]
  have hpair :
      Summable (fun p : ℕ × ℕ => firstEntryPairWeight x Y p) :=
    (summable_prod_of_nonneg hpair_nonneg).2 ⟨hslice, hrow_summable⟩
  have hfiber :
      HasSum
        (fun n : ℕ =>
          ∑' p : (fun mq : ℕ × ℕ => mq.1 * mq.2) ⁻¹' ({n} : Set ℕ),
            firstEntryPairWeight x Y p)
        (∑' p : ℕ × ℕ, firstEntryPairWeight x Y p) :=
    HasSum.tsum_fiberwise hpair.hasSum (fun mq : ℕ × ℕ => mq.1 * mq.2)
  have hfirst :
      HasSum (fun n : ℕ => normalizationFirstEntryPart x Y n)
        (∑' p : ℕ × ℕ, firstEntryPairWeight x Y p) := by
    convert hfiber using 1
    ext n
    simpa using (tsum_firstEntryPairWeight_fiber_prod (x := x) (Y := Y) (n := n) hx).symm
  have hrows :
      ∑' p : ℕ × ℕ, firstEntryPairWeight x Y p = ∑' m : ℕ, row m := by
    simpa [row] using hpair.tsum_prod' hslice
  rw [hrows] at hfirst
  rw [tsum_eq_sum (s := Finset.Icc 1 (x - 1)) hrow_zero] at hfirst
  convert hfirst using 1
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [hrow m, if_pos]
  simpa [hIcc m] using hm

/--
For fixed `Y ≥ 2`, the first-entry contribution to `B_x` is summable and equals
`1 + O(1 / log x)` as `x → ∞`.
-/
lemma normalizationFirstEntryPart_estimate {Y : ℕ} (hY : 2 ≤ Y) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ ⦃x : ℕ⦄, x₀ ≤ x →
        Summable (fun n : ℕ => normalizationFirstEntryPart x Y n) ∧
          |(∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1| ≤ C / Real.log (x : ℝ) := by
  rcases firstEntryTailApproximation (Y := Y) hY with ⟨C0, hC0pos, happrox⟩
  let x₀ : ℕ := max 3 ⌈Real.exp (C0 + 1)⌉₊
  refine ⟨1 + 2 * C0, by linarith, x₀, ?_⟩
  intro x hxx
  have hx3 : 3 ≤ x := le_trans (le_max_left 3 ⌈Real.exp (C0 + 1)⌉₊) hxx
  have hx2 : 2 ≤ x := le_trans (by decide : 2 ≤ 3) hx3
  have hx1 : 1 ≤ x := le_trans (by decide : 1 ≤ 3) hx3
  have hexp_le_x : Real.exp (C0 + 1) ≤ (x : ℝ) := by
    calc
      Real.exp (C0 + 1) ≤ (⌈Real.exp (C0 + 1)⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil _
      _ ≤ (x₀ : ℝ) := by
          exact_mod_cast (le_max_right 3 ⌈Real.exp (C0 + 1)⌉₊)
      _ ≤ (x : ℝ) := by exact_mod_cast hxx
  have hxlog_pos : 0 < Real.log (x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hx3))
  have hxlog_ne : Real.log (x : ℝ) ≠ 0 := hxlog_pos.ne'
  have hxlog_ge : C0 + 1 ≤ Real.log (x : ℝ) := by
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp_le_x
  have hsummable :
      ∀ {m : ℕ}, 1 ≤ m → m < x →
        Summable (fun q : ℕ =>
          if entryThreshold x Y m ≤ q then
            Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
          else 0) := by
    intro m hm1 hmx
    by_contra hs
    have hzero : firstEntryTail x Y m = 0 := by
      rw [firstEntryTail, tsum_eq_zero_of_not_summable hs]
    have hmain : 0 < 1 / Real.log (x : ℝ) - C0 / (Real.log (x : ℝ)) ^ 2 := by
      field_simp [hxlog_ne]
      nlinarith
    have hleft := (abs_le.mp (happrox hx2 hm1 hmx)).1
    rw [hzero] at hleft
    linarith
  have hfirst := hasSum_normalizationFirstEntryPart (x := x) (Y := Y) hx1 hsummable
  have hfirst_eq :
      ∑' n : ℕ, normalizationFirstEntryPart x Y n =
        ∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m := hfirst.tsum_eq
  let H : ℝ := ∑ m ∈ Finset.Icc 1 (x - 1), (1 : ℝ) / m
  let E : ℝ :=
    ∑ m ∈ Finset.Icc 1 (x - 1),
      (1 / (m : ℝ)) * (firstEntryTail x Y m - 1 / Real.log (x : ℝ))
  have hHabs : |H - Real.log (x : ℝ)| ≤ 1 := by
    simpa [H] using abs_sum_Icc_inv_sub_log_le_one x hx1
  have hEbound :
      |E| ≤ (2 * C0) / Real.log (x : ℝ) := by
    have hnorm :
        ‖∑ m ∈ Finset.Icc 1 (x - 1),
            (1 / (m : ℝ)) * (firstEntryTail x Y m - 1 / Real.log (x : ℝ))‖
          ≤ ∑ m ∈ Finset.Icc 1 (x - 1), (C0 / (Real.log (x : ℝ)) ^ 2) * (1 / (m : ℝ)) := by
      refine norm_sum_le_of_le _ ?_
      intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨hm1, hmx_le⟩
      have hmx : m < x := by omega
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg]
      · simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_of_nonneg_left (happrox hx2 hm1 hmx) (by positivity : 0 ≤ 1 / (m : ℝ)))
      · positivity
    calc
      |E| ≤ (C0 / (Real.log (x : ℝ)) ^ 2) * H := by
        simpa [E, H, Finset.mul_sum, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using
          hnorm
      _ ≤ (C0 / (Real.log (x : ℝ)) ^ 2) * (Real.log (x : ℝ) + 1) := by
            gcongr
            linarith [(abs_le.mp hHabs).2]
      _ ≤ (2 * C0) / Real.log (x : ℝ) := by
            field_simp [hxlog_ne]
            nlinarith [hC0pos, hxlog_ge]
  have hsplit :
      ∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m =
        (1 / Real.log (x : ℝ)) * H + E := by
    calc
      ∑ m ∈ Finset.Icc 1 (x - 1), (1 / (m : ℝ)) * firstEntryTail x Y m
        = ∑ m ∈ Finset.Icc 1 (x - 1),
            ((1 / Real.log (x : ℝ)) * (1 / (m : ℝ)) +
              (1 / (m : ℝ)) * (firstEntryTail x Y m - 1 / Real.log (x : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              ring
      _ = (1 / Real.log (x : ℝ)) * H + E := by
            simp [H, E, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
  refine ⟨hfirst.summable, ?_⟩
  calc
    |(∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1|
      = |((H - Real.log (x : ℝ)) / Real.log (x : ℝ)) + E| := by
          rw [hfirst_eq, hsplit]
          have hrew :
              (1 / Real.log (x : ℝ)) * H + E - 1 =
                ((H - Real.log (x : ℝ)) / Real.log (x : ℝ)) + E := by
            field_simp [hxlog_ne]
            ring
          simpa [sub_eq_add_neg] using congrArg abs hrew
    _ ≤ |(H - Real.log (x : ℝ)) / Real.log (x : ℝ)| + |E| := abs_add_le _ _
    _ ≤ 1 / Real.log (x : ℝ) + |E| := by
          gcongr
          rw [abs_div, abs_of_pos hxlog_pos]
          exact div_le_div_of_nonneg_right hHabs (le_of_lt hxlog_pos)
    _ ≤ 1 / Real.log (x : ℝ) + (2 * C0) / Real.log (x : ℝ) := by
          gcongr
    _ = (1 + 2 * C0) / Real.log (x : ℝ) := by ring
end PrimitiveSetsAboveX
