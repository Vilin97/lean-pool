/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # MissingMathlib.lean
  Small convenience lemmas likely to stay project-local.

  This file collects small reusable lemmas that are convenient to prove
  once and reuse downstream.
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.Definitions
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # MissingMathlib -/


open Complex MeasureTheory Real Finset Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace HermiteLEAN

-- to_mathlib: Mathlib/Data/Finset/Intervals
/-- Square blocks have the expected odd cardinality. -/
theorem squareBlock_card (ℓ : ℕ) : (squareBlock ℓ).card = 2 * ℓ + 1 := by
  rw [squareBlock, Nat.card_Ico, pow_two, pow_two]
  have h : (ℓ + 1) * (ℓ + 1) = ℓ * ℓ + (2 * ℓ + 1) := by
    ring
  rw [h]
  exact Nat.add_sub_cancel_left (ℓ * ℓ) (2 * ℓ + 1)

-- to_mathlib: Mathlib/Data/Real/Interval
/-- A convenient interval-distance lower bound for annulus arguments. -/
theorem annulus_distance_lower_bound (j : ℕ) (x : ℝ) :
    posPart (|((j : ℕ) : ℝ) - x| - 1)
      ≤ min |((j : ℕ) : ℝ) - x| |(((j + 1 : ℕ) : ℝ) - x)| := by
  dsimp [posPart]
  set a : ℝ := |((j : ℕ) : ℝ) - x|
  set b : ℝ := |(((j + 1 : ℕ) : ℝ) - x)|
  have ha0 : 0 ≤ a := by
    simp [a]
  have hb0 : 0 ≤ b := by
    simp [b]
  have h1 : max (a - 1) 0 ≤ a := by
    exact max_le (by linarith) ha0
  have habs : |a - b| ≤ 1 := by
    have h := abs_abs_sub_abs_le_abs_sub ((j : ℝ) - x) ((((j + 1 : ℕ) : ℝ) - x))
    have hrhs : |((j : ℝ) - x) - ((((j + 1 : ℕ) : ℝ) - x))| = 1 := by
      ring_nf
      simp
    simpa [a, b, hrhs] using h
  have h2' : a - 1 ≤ b := by
    have hrewrite : a - b ≤ 1 := (abs_sub_le_iff.mp habs).1
    linarith
  have h2 : max (a - 1) 0 ≤ b := by
    exact max_le h2' hb0
  exact le_min h1 h2

-- to_mathlib: Mathlib/Analysis/SpecialFunctions/Gaussian/Basic
/-- A reusable Gaussian absorption lemma. -/
theorem polynomial_times_gaussian_le_gaussian
    {a : ℝ}
    (ha : 0 < a)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 0 ≤ x →
        (1 + x ^ k) * Real.exp (-a * x ^ 2)
          ≤ C * Real.exp (-(a / 2) * x ^ 2) := by
  let g : ℝ → ℝ := fun x => (1 + x ^ k) * Real.exp (-(a / 2) * x ^ 2)
  have hsq : Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(a / 2) * x ^ 2)) Filter.atTop (𝓝 0) := by
    have hmul : Tendsto (fun x : ℝ => (-(a / 2)) * (x ^ 2)) Filter.atTop Filter.atBot := by
      exact hsq.const_mul_atTop_of_neg (by nlinarith [ha])
    convert Real.tendsto_exp_atBot.comp hmul using 1 with x
  have hpoly : Tendsto (fun x : ℝ => x ^ k * Real.exp (-(a / 2) * x ^ 2)) Filter.atTop (𝓝 0) := by
    refine Tendsto.congr' ?_
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / 2) (a / 2) (by positivity)).comp
        hsq)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    change ((x ^ 2 : ℝ) ^ ((k : ℝ) / 2)) * Real.exp (-(a / 2) * (x ^ 2)) =
      x ^ k * Real.exp (-(a / 2) * x ^ 2)
    rw [show x ^ k = x ^ ((k : ℝ)) by rw [Real.rpow_natCast]]
    congr 1
    calc
      ((x ^ 2 : ℝ) ^ ((k : ℝ) / 2)) = x ^ ((((2 : ℕ) : ℝ)) * ((k : ℝ) / 2)) := by
        rw [← Real.rpow_natCast_mul hx 2 ((k : ℝ) / 2)]
      _ = x ^ ((k : ℝ)) := by
        congr 2
        ring
  have hgtendsto : Tendsto g Filter.atTop (𝓝 0) := by
    have hsum := hexp.add hpoly
    convert hsum using 1 <;> ext x <;> simp [g, add_mul]
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop, g x < 1 := by
    exact (tendsto_order.1 hgtendsto).2 1 zero_lt_one
  rcases Filter.eventually_atTop.1 hsmall with ⟨R, hR⟩
  have hcont : Continuous g := by
    dsimp [g]
    exact (continuous_const.add <| continuous_id.pow k).mul <|
      Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))
  have hcompactIcc : IsCompact (Set.Icc 0 R) := isCompact_Icc
  obtain ⟨C0, hC0⟩ := hcompactIcc.exists_bound_of_continuousOn (hcont.continuousOn)
  let C : ℝ := |C0| + 1
  refine ⟨C, by positivity, ?_⟩
  intro x hx
  have hbound_g : g x ≤ C := by
    by_cases hxr : x ≤ R
    · have hxmem : x ∈ Set.Icc 0 R := ⟨hx, hxr⟩
      have honepow_nonneg : 0 ≤ 1 + x ^ k := by positivity
      have hcompact : g x ≤ C0 := by
        simpa [Real.norm_eq_abs, g, abs_of_nonneg honepow_nonneg] using hC0 x hxmem
      have hC0leC : C0 ≤ C := by
        dsimp [C]
        linarith [le_abs_self C0]
      exact hcompact.trans hC0leC
    · have hxR : R ≤ x := le_of_not_ge hxr
      have htail : g x < 1 := hR x hxR
      have hone_le : 1 ≤ C := by
        dsimp [C]
        nlinarith [abs_nonneg C0]
      exact htail.le.trans hone_le
  have hsplit :
      Real.exp (-a * x ^ 2) =
        Real.exp (-(a / 2) * x ^ 2) * Real.exp (-(a / 2) * x ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (1 + x ^ k) * Real.exp (-a * x ^ 2)
      = (1 + x ^ k) * (Real.exp (-(a / 2) * x ^ 2) * Real.exp (-(a / 2) * x ^ 2)) := by
          rw [hsplit]
    _ = g x * Real.exp (-(a / 2) * x ^ 2) := by
          simp [g, mul_left_comm, mul_comm]
    _ ≤ C * Real.exp (-(a / 2) * x ^ 2) := by
          have hexp_nonneg : 0 ≤ Real.exp (-(a / 2) * x ^ 2) := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hbound_g hexp_nonneg

end HermiteLEAN
