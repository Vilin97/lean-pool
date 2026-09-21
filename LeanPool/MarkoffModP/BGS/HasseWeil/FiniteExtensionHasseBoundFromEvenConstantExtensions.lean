/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaDegreeIndexOneAutomatic
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaHasseBound

/-!
# Hasse bounds from even exact constant-extension estimates

This file connects the exact constant-extension closed-place identity to the
completed zeta-function and spectral arguments.  A uniform two-sided estimate
for degree-one places on the exact degree-`2n` constant extensions becomes the
even-extension `IsBigO` premise used by the power-sum argument.  Exact
constants then provide the zeta numerator and its degree bound automatically.

The geometric two-sided estimate itself is deliberately left as an explicit
hypothesis.  Proving it is the remaining Galois-twist boundary; no one-sided
Stepanov estimate can replace it.
-/

namespace BGS.HasseWeil

open Filter Asymptotics

noncomputable section

/-- Pointwise two-sided square-root estimates at every positive even-extension
index imply the asymptotic estimate used by the zeta spectral argument. -/
theorem evenExtensionError_isBigO_of_pointwise_bound
    (q : ℕ) (pointCount : ℕ → ℕ) (A : ℝ)
    (hbound : ∀ n, 0 < n →
      |(pointCount (2 * n) : ℝ) - (q : ℝ) ^ (2 * n) - 1| ≤
        A * (q : ℝ) ^ n) :
    (fun n : ℕ ↦
      (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =O[atTop]
        fun n : ℕ ↦ (q : ℝ) ^ n := by
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hqn : 0 ≤ (q : ℝ) ^ n := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hqn]
  have heq :
      (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1 =
        (((pointCount (2 * n) : ℝ) - (q : ℝ) ^ (2 * n) - 1 : ℝ) : ℂ) := by
    norm_num
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact hbound n hn

/-- A pointwise two-sided square-root estimate along one fixed divisible-even
subsequence, with a bounded additive error, gives the asymptotic estimate
used by the rank-general spectral argument. -/
theorem divisibleEvenExtensionError_isBigO_of_pointwise_bound
    (q δ : ℕ) (pointCount : ℕ → ℕ) (A B : ℝ)
    (hq : 0 < q) (hA : 0 ≤ A)
    (hbound : ∀ n, 0 < n →
      |(pointCount (2 * δ * n) : ℝ) -
          (q : ℝ) ^ (2 * δ * n) - 1| ≤
        A + B * (((q : ℝ) ^ δ) ^ n)) :
    (fun n : ℕ ↦
      (pointCount (2 * δ * n) : ℂ) -
        (q : ℂ) ^ (2 * δ * n) - 1) =O[atTop]
      fun n : ℕ ↦ ((q : ℝ) ^ δ) ^ n := by
  apply IsBigO.of_bound (A + B)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hqOneNat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne'
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqOneNat
  have hrhoOne : (1 : ℝ) ≤ ((q : ℝ) ^ δ) ^ n :=
    one_le_pow₀ (one_le_pow₀ hqOne)
  have hpoint := hbound n hnpos
  have heq :
      (pointCount (2 * δ * n) : ℂ) -
          (q : ℂ) ^ (2 * δ * n) - 1 =
        (((pointCount (2 * δ * n) : ℝ) -
          (q : ℝ) ^ (2 * δ * n) - 1 : ℝ) : ℂ) := by
    norm_num
  have hrhoNonneg : 0 ≤ (((q : ℝ) ^ δ) ^ n) := by positivity
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hrhoNonneg]
  calc
    |(pointCount (2 * δ * n) : ℝ) -
        (q : ℝ) ^ (2 * δ * n) - 1| ≤
      A + B * (((q : ℝ) ^ δ) ^ n) := hpoint
    _ ≤ (A + B) * (((q : ℝ) ^ δ) ^ n) := by nlinarith

variable (C N : Type*) [Field C] [Fintype C]
  [DecidableEq C] [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]

local instance evenConstantExtensionBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance evenConstantExtensionBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The exact constant-extension count identity transports a pointwise
two-sided estimate for rational places on every canonical degree-`2n`
constant extension to the even-extension `IsBigO` estimate for the original
closed-place count sequence. -/
theorem finiteExtensionClosedPlaceEvenError_isBigO_of_exactConstantExtension_bound
    (p : ℕ) [Fact p.Prime] [CharP C p]
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (A : ℝ)
    (hbound : ∀ n (hn : 0 < n),
      letI : NeZero (2 * n) := ⟨by omega⟩
      let S := FiniteField.Extension C p (2 * n)
      letI : Fintype S := Fintype.ofFinite S
      |(exactConstantExtensionClosedPlaceExtensionCount
          C S N hExact 1 : ℝ) - (Nat.card S : ℝ) - 1| ≤
        A * (Nat.card C : ℝ) ^ n) :
    (fun n : ℕ ↦
      (finiteExtensionClosedPlaceExtensionCount C N (2 * n) : ℂ) -
        (Nat.card C : ℂ) ^ (2 * n) - 1) =O[atTop]
      fun n : ℕ ↦ (Nat.card C : ℝ) ^ n := by
  apply evenExtensionError_isBigO_of_pointwise_bound
  intro n hn
  letI : NeZero (2 * n) := ⟨by omega⟩
  let S := FiniteField.Extension C p (2 * n)
  letI : Fintype S := Fintype.ofFinite S
  have hcount :
      exactConstantExtensionClosedPlaceExtensionCount C S N hExact 1 =
        finiteExtensionClosedPlaceExtensionCount C N (2 * n) := by
    rw [exactConstantExtensionClosedPlaceExtensionCount_eq_classical_decidableEq]
    have h := exactConstantExtensionClosedPlaceExtensionCount_eq
      C S N hExact 1
    have hfinrank : Module.finrank C S = 2 * n := by
      simpa [S] using FiniteField.finrank_extension C p (2 * n)
    rw [hfinrank, Nat.mul_one] at h
    convert h using 1
    all_goals congr 1
  have hcard : Nat.card S = Nat.card C ^ (2 * n) := by
    simpa [S] using FiniteField.natCard_extension C p (2 * n)
  have hreal := hbound n hn
  dsimp only [S] at hreal
  rw [hcount, hcard] at hreal
  simpa only [Nat.cast_pow] using hreal

/-- Exact constants make the standard zeta numerator automatic.  Hence the
even-extension error estimate is the only analytic premise left for the
closed-place Hasse bound, apart from the stated genus budget. -/
theorem finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_evenError
    (budget : ℕ)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hgenus : FunctionField.genus C N ≤ budget)
    (herror :
      (fun n : ℕ ↦
        (finiteExtensionClosedPlaceExtensionCount C N (2 * n) : ℂ) -
          (Nat.card C : ℂ) ^ (2 * n) - 1) =O[atTop]
        fun n : ℕ ↦ (Nat.card C : ℝ) ^ n) :
    |(finiteExtensionClosedPlaceExtensionCount C N 1 : ℝ) -
        Nat.card C - 1| ≤
      (2 * budget + 1 : ℝ) * Real.sqrt (Nat.card C) := by
  obtain ⟨P, hPzero, _hPone, hPdegree, hPrational, _hPtrace⟩ :=
    exists_finiteExtensionClosedPlaceZeta_trace_with_degree_budget_of_exactConstants
      C N budget hExact hgenus
  have hbound :=
    abs_pointCount_sub_card_sub_one_le_of_formalPointCountZeta_rational_and_evenError_isBigO
      (Nat.card C) (finiteExtensionClosedPlaceExtensionCount C N) P
        hPzero hPrational herror
  calc
    |(finiteExtensionClosedPlaceExtensionCount C N 1 : ℝ) -
        Nat.card C - 1| ≤
      (P.natDegree : ℝ) * Real.sqrt (Nat.card C) := hbound
    _ ≤ (2 * budget + 1 : ℝ) * Real.sqrt (Nat.card C) := by
      gcongr
      exact_mod_cast hPdegree

/-- Exact constants make the zeta package automatic also when the geometric
error estimate is available only along one fixed positive divisible-even
subsequence. -/
theorem
    finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_divisibleEvenError
    (budget δ : ℕ)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hgenus : FunctionField.genus C N ≤ budget)
    (hδ : 0 < δ)
    (herror :
      (fun n : ℕ ↦
        (finiteExtensionClosedPlaceExtensionCount C N (2 * δ * n) : ℂ) -
          (Nat.card C : ℂ) ^ (2 * δ * n) - 1) =O[atTop]
        fun n : ℕ ↦ ((Nat.card C : ℝ) ^ δ) ^ n) :
    |(finiteExtensionClosedPlaceExtensionCount C N 1 : ℝ) -
        Nat.card C - 1| ≤
      (2 * budget + 1 : ℝ) * Real.sqrt (Nat.card C) := by
  obtain ⟨P, hPzero, _hPone, hPdegree, hPrational, _hPtrace⟩ :=
    exists_finiteExtensionClosedPlaceZeta_trace_with_degree_budget_of_exactConstants
      C N budget hExact hgenus
  have hbound :=
    abs_pointCount_sub_card_sub_one_le_of_formalPointCountZeta_rational_and_divisibleEvenError_isBigO
      (Nat.card C) δ (finiteExtensionClosedPlaceExtensionCount C N) P
        Nat.card_pos hδ hPzero hPrational herror
  calc
    |(finiteExtensionClosedPlaceExtensionCount C N 1 : ℝ) -
        Nat.card C - 1| ≤
      (P.natDegree : ℝ) * Real.sqrt (Nat.card C) := hbound
    _ ≤ (2 * budget + 1 : ℝ) * Real.sqrt (Nat.card C) := by
      gcongr
      exact_mod_cast hPdegree

/-- The selected Lorenzini endpoint at the spectral boundary.  A uniform
pointwise two-sided estimate along one positive divisible-even subsequence,
allowing a fixed additive error, implies the degree-one closed-place Hasse
bound.  Exact constants supply the zeta numerator, index one, and the trace
formula internally. -/
theorem
    finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_divisibleEvenError_bound
    (budget δ : ℕ)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hgenus : FunctionField.genus C N ≤ budget)
    (hδ : 0 < δ)
    (A B : ℝ)
    (hA : 0 ≤ A)
    (hbound : ∀ n, 0 < n →
      |(finiteExtensionClosedPlaceExtensionCount C N (2 * δ * n) : ℝ) -
          (Nat.card C : ℝ) ^ (2 * δ * n) - 1| ≤
        A + B * (((Nat.card C : ℝ) ^ δ) ^ n)) :
    |(finiteExtensionClosedPlaceExtensionCount C N 1 : ℝ) -
        Nat.card C - 1| ≤
      (2 * budget + 1 : ℝ) * Real.sqrt (Nat.card C) := by
  apply
    finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_divisibleEvenError
      C N budget δ hExact hgenus hδ
  exact divisibleEvenExtensionError_isBigO_of_pointwise_bound
    (Nat.card C) δ (finiteExtensionClosedPlaceExtensionCount C N)
      A B Nat.card_pos hA hbound

/-- The fully connected conditional endpoint: a uniform two-sided estimate
for rational places on the canonical even exact constant extensions implies
the base closed-place Hasse bound.  Zeta rationality, the trace formula, and
degree index one are all discharged internally. -/
theorem finiteExtensionClosedPlaceHasseBound_of_evenExactConstantExtension_bound
    (p : ℕ) [Fact p.Prime] [CharP C p]
    (budget : ℕ)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hgenus : FunctionField.genus C N ≤ budget)
    (A : ℝ)
    (hbound : ∀ n (hn : 0 < n),
      letI : NeZero (2 * n) := ⟨by omega⟩
      let S := FiniteField.Extension C p (2 * n)
      letI : Fintype S := Fintype.ofFinite S
      |(exactConstantExtensionClosedPlaceExtensionCount
          C S N hExact 1 : ℝ) - (Nat.card S : ℝ) - 1| ≤
        A * (Nat.card C : ℝ) ^ n) :
    |(finiteExtensionClosedPlaceExtensionCount C N 1 : ℝ) -
        Nat.card C - 1| ≤
      (2 * budget + 1 : ℝ) * Real.sqrt (Nat.card C) := by
  apply finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_evenError
    C N budget hExact hgenus
  exact
    finiteExtensionClosedPlaceEvenError_isBigO_of_exactConstantExtension_bound
      C N p hExact A hbound

end

end BGS.HasseWeil
