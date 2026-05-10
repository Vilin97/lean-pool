/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import LeanPool.Erdos1196.Main
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The formal-conjectures statement of Erdős Problem 1196

This file packages the local solution of Erdős Problem `#1196` in the mathematical form used by
the `formal-conjectures` repository. We keep the same namespace, theorem name, and primitive-set
definition, but omit the repository-specific metadata attribute and `answer(...)` wrapper.

## Main statements

* `Erdos1196.IsPrimitive`
* `Erdos1196.erdos_1196`
-/

open Filter
open scoped Asymptotics BigOperators

namespace Erdos1196

/-- Exact local copy of the primitive-set predicate used in the official
`formal-conjectures` statement of Erdős Problem `#1196`. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y

private lemma log_pos_nat {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  exact Real.log_pos <| by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)

private lemma div_lt_abs_add_one_div {C t : ℝ} (ht : 0 < t) :
    C / t < (|C| + 1) / t := by
  field_simp [ht.ne']
  nlinarith [le_abs_self C]

private lemma isPrimitive_nat_iff (A : Set ℕ) :
    IsPrimitive A ↔ PrimitiveSetsAboveX.PrimitiveSet A := by
  constructor
  · intro h m n hm hn hmn
    exact associated_iff_eq.mp <| h m hm n hn hmn
  · intro h m hm n hn hmn
    exact associated_iff_eq.mpr <| h hm hn hmn

private lemma logSeries_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  by_cases h1 : n = 1
  · simp [h1]
  · have hn2 : 2 ≤ n := by omega
    have hlog : 0 ≤ Real.log (n : ℝ) := le_of_lt <| log_pos_nat hn2
    have hden : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
    simpa [mul_comm] using one_div_nonneg.mpr hden

private lemma tsum_subtype_eq_indicator_logSeries (A : Set ℕ) :
    ∑' (a : A), (1 / ((a.val : ℝ).log * a)) =
      ∑' n : ℕ, A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ))) n := by
  simpa [mul_comm] using tsum_subtype A (fun n : ℕ => 1 / ((n : ℝ) * Real.log (n : ℝ)))

/--
This is the `formal-conjectures`-style formulation of Erdős Problem `#1196`.
It is deduced from `PrimitiveSetsAboveX.mainTheorem` by converting the local quantitative bound
`1 + C / log x` into an `o(1)` error term.
-/
theorem erdos_1196 :
    ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
      ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
        ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x := by
  rcases PrimitiveSetsAboveX.mainTheorem with ⟨C, x₀, hx₀⟩
  let N := max x₀ 2
  have hN : x₀ ≤ N := le_max_left _ _
  have hNtwo : 2 ≤ N := le_max_right _ _
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log (n : ℝ))
  let headBound : ℕ → ℝ := fun x => (Finset.Icc x (N - 1)).sum f
  let o : ℕ → ℝ := fun x =>
    if hxN : x < N then
      headBound x + (|C| + 1) / Real.log (N : ℝ)
    else
      (|C| + 1) / Real.log (x : ℝ)
  refine ⟨o, ?_, ?_⟩
  · have ho_eq :
        o =ᶠ[Filter.atTop] fun x : ℕ => (|C| + 1) / Real.log (x : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop N] with x hx
      simp [o, not_lt.mpr hx]
    have hlog :
        Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hzero :
        Tendsto (fun x : ℕ => (|C| + 1) / Real.log (x : ℝ)) Filter.atTop (nhds 0) := by
      simpa using hlog.const_div_atTop (|C| + 1 : ℝ)
    exact (Asymptotics.isLittleO_one_iff ℝ).2 <| hzero.congr' ho_eq.symm
  · intro x hx_pos A hAx hPrimitive
    have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx_pos
    have hPrimitive' : PrimitiveSetsAboveX.PrimitiveSet A := (isPrimitive_nat_iff A).mp hPrimitive
    have hstrict {y : ℕ} (hy : N ≤ y) {B : Set ℕ} (hB : PrimitiveSetsAboveX.PrimitiveSet B)
        (hBy : B ⊆ Set.Ici y) :
        Summable (B.indicator f) ∧
          ∑' n : ℕ, B.indicator f n < 1 + (|C| + 1) / Real.log (y : ℝ) := by
      rcases hx₀ (le_trans hN hy) hB hBy with ⟨hBsummable, hBbound⟩
      have hlogy : 0 < Real.log (y : ℝ) := log_pos_nat (le_trans hNtwo hy)
      refine ⟨by simpa [f] using hBsummable, ?_⟩
      linarith [hBbound, div_lt_abs_add_one_div (C := C) hlogy]
    by_cases hxN : N ≤ x
    · rw [tsum_subtype_eq_indicator_logSeries A]
      simpa [f, o, not_lt.mpr hxN] using (hstrict hxN hPrimitive' hAx).2
    · have hxN' : x < N := lt_of_not_ge hxN
      let head : ℕ → ℝ := (A ∩ Set.Icc x (N - 1)).indicator f
      let tail : ℕ → ℝ := (A ∩ Set.Ici N).indicator f
      have hTailPrimitive : PrimitiveSetsAboveX.PrimitiveSet (A ∩ Set.Ici N) := by
        grind [PrimitiveSetsAboveX.PrimitiveSet]
      rcases hstrict (y := N) le_rfl hTailPrimitive (by intro n hn; exact hn.2) with
        ⟨hTailSummable', hTailLt⟩
      have hsplit (n : ℕ) :
          A.indicator f n = head n + tail n := by
        by_cases hnA : n ∈ A
        · have hxn : x ≤ n := hAx hnA
          by_cases hnN : n < N
          · have hHead : n ∈ Set.Icc x (N - 1) := by
              refine ⟨hxn, ?_⟩
              omega
            simp [head, tail, hnA, hHead, hnN.not_ge]
          · have hHead : n ∉ Set.Icc x (N - 1) := by
              intro hmem
              have hlt_top : N - 1 < N := Nat.sub_lt (show 0 < N by omega) (by decide)
              exact hnN (lt_of_le_of_lt hmem.2 hlt_top)
            simp [head, tail, hnA, hHead, not_lt.mp hnN]
        · simp [head, tail, hnA]
      have hHeadZero : ∀ n ∉ Finset.Icc x (N - 1), head n = 0 := by
        intro n hn
        have hn' : n ∉ Set.Icc x (N - 1) := by simpa using hn
        simp [head, hn']
      have hHeadSummable : Summable head := by
        refine summable_of_hasFiniteSupport ((Finset.Icc x (N - 1)).finite_toSet.subset ?_)
        intro n hn
        by_contra hnot
        exact hn (hHeadZero n hnot)
      have hHeadLe : (∑' n : ℕ, head n) ≤ headBound x := by
        rw [tsum_eq_sum (s := Finset.Icc x (N - 1)) hHeadZero]
        change
          (Finset.Icc x (N - 1)).sum head ≤
            (Finset.Icc x (N - 1)).sum f
        refine Finset.sum_le_sum ?_
        intro n hn
        by_cases hnA : n ∈ A
        · have hnSet : n ∈ Set.Icc x (N - 1) := by simpa using hn
          simp [f, hnA, hnSet]
        · have hn1 : 1 ≤ n := le_trans hx1 (Finset.mem_Icc.mp hn).1
          have hnSet : n ∈ Set.Icc x (N - 1) := by simpa using hn
          simpa [head, f, hnA, hnSet] using logSeries_nonneg hn1
      calc
        ∑' (a : A), (1 / ((a.val : ℝ).log * a))
          = ∑' n : ℕ, A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ))) n := by
              exact tsum_subtype_eq_indicator_logSeries A
        _ = ∑' n : ℕ, head n + ∑' n : ℕ, tail n := by
              rw [show
                (∑' n : ℕ, A.indicator f n) =
                  ∑' n : ℕ, (head n + tail n) by
                    refine tsum_congr ?_
                    intro n
                    exact hsplit n]
              simpa [Pi.add_apply] using Summable.tsum_add hHeadSummable hTailSummable'
        _ ≤ headBound x + ∑' n : ℕ, tail n := by
              exact add_le_add hHeadLe le_rfl
        _ < headBound x + (1 + (|C| + 1) / Real.log (N : ℝ)) := by
              linarith
        _ = 1 + o x := by
              simp [o, headBound, hxN']
              ring

end Erdos1196
