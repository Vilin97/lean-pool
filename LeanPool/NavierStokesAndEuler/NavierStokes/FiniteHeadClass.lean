/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Exact-weight exponent changes for finitely many initial bands

Only the band exponent changes.  The weight, domain, polynomial degree,
and finite band cutoff are preserved, including at the spatial edges.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.FiniteHeadClass

open Set WeightedClasses
open scoped BigOperators ContDiff

variable {D E : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One constant, independent of the point and derivative order, compares
the two exponents on the fixed finite set of bands. -/
noncomputable def comparison (s : StripData D) (N : ℕ) (α β : ℝ) : ℝ :=
  1 + ∑ n ∈ Finset.range N, s.epsilon n ^ (α - β)

theorem one_le_comparison (s : StripData D) (N : ℕ) (α β : ℝ) :
    1 ≤ comparison s N α β := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun n _ => (Real.rpow_pos_of_pos (s.epsilon_pos n) _).le)

theorem comparison_nonneg (s : StripData D) (N : ℕ) (α β : ℝ) :
    0 ≤ comparison s N α β := zero_le_one.trans (one_le_comparison s N α β)

theorem ratio_le_comparison (s : StripData D) {N n : ℕ} (hn : n < N) (α β : ℝ) :
    s.epsilon n ^ (α - β) ≤ comparison s N α β := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.range N) =>
      (Real.rpow_pos_of_pos (s.epsilon_pos k) (α - β)).le)
    (Finset.mem_range.mpr hn)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem exponent_le (s : StripData D) {N n : ℕ} (hn : n < N) (α β : ℝ) :
    s.epsilon n ^ α ≤ comparison s N α β * s.epsilon n ^ β := by
  calc
    _ = s.epsilon n ^ (α - β) * s.epsilon n ^ β := by
      rw [← Real.rpow_add (s.epsilon_pos n)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (ratio_le_comparison s hn α β)
      (Real.rpow_pos_of_pos (s.epsilon_pos n) β).le

/-- No derivative of the weight or spatial cutoff is used here. -/
theorem majorant_le {s : StripData D} {w : ℕ → D → ℝ} {α β C : ℝ}
    {N n p : ℕ} {x : D} (hn : n < N) (hC : 0 ≤ C) (hw : 0 ≤ w n x) :
    majorant s w α C p n x ≤
      majorant s w β (C * comparison s N α β) p n x := by
  unfold majorant
  apply mul_le_mul_of_nonneg_right _ hw
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (s.growth_nonneg n x) p)
  calc
    _ ≤ C * (comparison s N α β * s.epsilon n ^ β) :=
      mul_le_mul_of_nonneg_left (exponent_le s hn α β) hC
    _ = _ := (mul_assoc _ _ _).symm

/-- Vanishing on the same open domain gives vanishing of every actual
ambient derivative there, without any global vanishing assumption. -/
theorem jet_eq_zero {s : StripData D} {f : D → E}
    (hz : ∀ x ∈ s.domain, f x = 0) {x : D} (hx : x ∈ s.domain) (j : ℕ) :
    iteratedFDeriv ℝ j f x = 0 := by
  have he : EqOn f (fun _ => (0 : E)) s.domain := fun y hy => hz y hy
  have hd := iteratedFDerivWithin_congr (𝕜 := ℝ) he hx j
  rw [iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx,
    iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx] at hd
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hd

/-- Quantitative exponent transfer for a finite prefix of actual jets.
The initial bound is needed only on `n < N`. Its degree `p` is unchanged.
The multiplier works uniformly for any additional labels in the data. -/
theorem jet_bound {s : StripData D} {w : ℕ → D → ℝ} {f : ℕ → D → E}
    {N m p : ℕ} {α β C : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) (hC : 0 ≤ C)
    (hb : ∀ n, n < N → ∀ x, x ∈ s.domain → ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s w α C p n x)
    (hz : ∀ n, N ≤ n → ∀ x ∈ s.domain, f n x = 0) :
    ∀ n x, x ∈ s.domain → ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤
        majorant s w β (C * comparison s N α β) p n x := by
  intro n x hx j hj
  by_cases hn : n < N
  · exact (hb n hn x hx j hj).trans (majorant_le hn hC (hw n x hx))
  · rw [jet_eq_zero (hz n (Nat.le_of_not_gt hn)) hx j, norm_zero]
    exact majorant_nonneg s w β (mul_nonneg hC (comparison_nonneg s N α β))
      p n x (hw n x hx)

/-- A weighted class supported in the fixed finite initial bands has any
chosen exponent with exactly the original weight. -/
theorem memClass_of_finite_bands {s : StripData D} {w : ℕ → D → ℝ}
    {α β : ℝ} {f : ℕ → D → E} (hf : MemClass s w α f) (N : ℕ)
    (hz : ∀ n, N ≤ n → ∀ x ∈ s.domain, f n x = 0) : MemClass s w β f := by
  refine ⟨hf.weight_nonneg, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C * comparison s N α β, mul_nonneg hC (comparison_nonneg s N α β), p, ?_⟩
  exact jet_bound hf.weight_nonneg hC (fun n _ => hb n) hz

theorem all_exponents {s : StripData D} {w : ℕ → D → ℝ}
    {α : ℝ} {f : ℕ → D → E} (hf : MemClass s w α f) (N : ℕ)
    (hz : ∀ n, N ≤ n → ∀ x ∈ s.domain, f n x = 0) :
    ∀ β : ℝ, MemClass s w β f := fun _ => memClass_of_finite_bands hf N hz

/-- The radial weight `zeta` is retained at the same spatial edges. -/
theorem meanClass_all_exponents {s : StripData D} {α : ℝ} {f : ℕ → D → E}
    (hf : MeanClass s α f) (N : ℕ)
    (hz : ∀ n, N ≤ n → ∀ x ∈ s.domain, f n x = 0) :
    ∀ β : ℝ, MeanClass s β f := all_exponents hf N hz

/-- Both the square-root radial weight and the given slot envelope remain
exactly the same; no lower bound for either is required. -/
theorem waveClass_all_exponents {s : StripData D} {P : ℕ → D → ℝ}
    {α : ℝ} {f : ℕ → D → E} (hf : WaveClass s P α f) (N : ℕ)
    (hz : ∀ n, N ≤ n → ∀ x ∈ s.domain, f n x = 0) :
    ∀ β : ℝ, WaveClass s P β f := all_exponents hf N hz

theorem unweightedClass_all_exponents {s : StripData D}
    {α : ℝ} {f : ℕ → D → E} (hf : UnweightedClass s α f) (N : ℕ)
    (hz : ∀ n, N ≤ n → ∀ x ∈ s.domain, f n x = 0) :
    ∀ β : ℝ, UnweightedClass s β f := all_exponents hf N hz

end NavierStokes.FiniteHeadClass
