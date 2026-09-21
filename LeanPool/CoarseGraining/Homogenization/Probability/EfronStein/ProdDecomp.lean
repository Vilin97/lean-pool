/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import LeanPool.CoarseGraining.Homogenization.Probability.EfronStein.TwoPoint

/-!
# Two-factor variance decomposition

The "law of total variance" for a product of two probability measures, proved by
direct Fubini computation for *bounded* observables (no `condExp`).

* `Homogenization.variance_prod_eq`: for a bounded measurable `F : α × β → ℝ`
  and probability measures `P, Q`,
  `Var[F; P ⊗ Q] = ∫ b, Var[F(·,b); P] dQ + Var[b ↦ ∫ F(·,b) dP; Q]`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Homogenization

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- **Two-factor variance decomposition** (law of total variance for a product of
two probability measures), bounded-observable form.  Here the first coordinate is
"integrated out": `g b := ∫ a, F (a, b) ∂P` is the conditional mean. -/
theorem variance_prod_eq {F : α × β → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ p, |F p| ≤ M) :
    Var[F; P.prod Q]
      = (∫ b, Var[fun a => F (a, b); P] ∂Q)
        + Var[fun b => ∫ a, F (a, b) ∂P; Q] := by
  classical
  set g : β → ℝ := fun b => ∫ a, F (a, b) ∂P with hg_def
  set m : ℝ := ∫ p, F p ∂(P.prod Q) with hm_def
  -- basic measurability / integrability
  have hFab : ∀ b, Measurable fun a => F (a, b) := fun b =>
    hF.comp (measurable_id.prodMk measurable_const)
  have hFab_int : ∀ b, Integrable (fun a => F (a, b)) P := fun b =>
    integrable_of_bound P (hFab b) (fun a => hM _)
  have hg : Measurable g := hF.stronglyMeasurable.integral_prod_left'.measurable
  have hgb : ∀ b, g b = ∫ a, F (a, b) ∂P := fun b => by simp only [hg_def]
  have hFint : Integrable F (P.prod Q) := integrable_of_bound _ hF hM
  -- `g` is bounded by `M`
  have hMg : ∀ b, |g b| ≤ M := by
    intro b
    rw [hgb b]
    calc |∫ a, F (a, b) ∂P| ≤ ∫ a, |F (a, b)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _a, M ∂P := integral_mono (hFab_int b).abs (integrable_const M) (fun a => hM _)
      _ = M := by simp
  -- `m = ∫ g` under `Q`
  have hmg : m = ∫ b, g b ∂Q := by
    rw [hm_def, integral_prod_symm F hFint]
  -- pointwise bound on the centred difference
  have hdmeas : ∀ b, Measurable fun a => F (a, b) - g b := fun b =>
    (hFab b).sub measurable_const
  have hdbound : ∀ b a, |F (a, b) - g b| ≤ 2 * M := by
    intro b a
    have h := abs_add_le (F (a, b)) (-(g b))
    rw [← sub_eq_add_neg, abs_neg] at h
    calc |F (a, b) - g b| ≤ |F (a, b)| + |g b| := h
      _ ≤ M + M := add_le_add (hM _) (hMg b)
      _ = 2 * M := by ring
  -- key pointwise-in-`b` identity
  have key : ∀ b, ∫ a, (F (a, b) - m) ^ 2 ∂P
      = (∫ a, (F (a, b) - g b) ^ 2 ∂P) + (g b - m) ^ 2 := by
    intro b
    have hFdiff : Integrable (fun a => F (a, b) - g b) P := (hFab_int b).sub (integrable_const _)
    have hAint : Integrable (fun a => (F (a, b) - g b) ^ 2) P :=
      integrable_sq_of_bound P (hdmeas b) (hdbound b)
    have hBint : Integrable (fun a => (2 * (g b - m)) * (F (a, b) - g b)) P := hFdiff.const_mul _
    have hAB : Integrable
        (fun a => (F (a, b) - g b) ^ 2 + (2 * (g b - m)) * (F (a, b) - g b)) P := hAint.add hBint
    have hcenter : ∫ a, (F (a, b) - g b) ∂P = 0 := by
      rw [integral_sub (hFab_int b) (integrable_const _), integral_const, ← hgb b]; simp
    have hexp : ∀ a, (F (a, b) - m) ^ 2
        = (F (a, b) - g b) ^ 2 + (2 * (g b - m)) * (F (a, b) - g b) + (g b - m) ^ 2 := by
      intro a; ring
    calc
      ∫ a, (F (a, b) - m) ^ 2 ∂P
          = ∫ a, ((F (a, b) - g b) ^ 2 + (2 * (g b - m)) * (F (a, b) - g b)
              + (g b - m) ^ 2) ∂P := by simp_rw [hexp]
      _ = (∫ a, (F (a, b) - g b) ^ 2 ∂P)
            + (2 * (g b - m)) * (∫ a, (F (a, b) - g b) ∂P) + (g b - m) ^ 2 := by
            rw [integral_add hAB (integrable_const _),
              integral_add hAint hBint, integral_const_mul, integral_const]
            simp
      _ = (∫ a, (F (a, b) - g b) ^ 2 ∂P) + (g b - m) ^ 2 := by rw [hcenter]; ring
  -- variance rewrites
  have hVb : ∀ b, Var[fun a => F (a, b); P] = ∫ a, (F (a, b) - g b) ^ 2 ∂P := by
    intro b
    rw [variance_eq_integral (hFab b).aemeasurable]
  have hVg : Var[g; Q] = ∫ b, (g b - m) ^ 2 ∂Q := by
    rw [variance_eq_integral hg.aemeasurable, ← hmg]
  -- LHS via Fubini
  have hFm_bound : ∀ p, |F p - m| ≤ M + |m| := by
    intro p
    have h := abs_add_le (F p) (-m)
    rw [← sub_eq_add_neg, abs_neg] at h
    exact h.trans (add_le_add (hM p) le_rfl)
  have hFm_int : Integrable (fun p => (F p - m) ^ 2) (P.prod Q) :=
    integrable_sq_of_bound _ (hF.sub measurable_const) hFm_bound
  have hLHS : Var[F; P.prod Q] = ∫ b, ∫ a, (F (a, b) - m) ^ 2 ∂P ∂Q := by
    rw [variance_eq_integral hFint.aemeasurable, ← hm_def,
      integral_prod_symm (fun p => (F p - m) ^ 2) hFm_int]
  -- integrability of the two `Q`-integrands in the decomposition
  have hI2 : Integrable (fun b => (g b - m) ^ 2) Q :=
    integrable_sq_of_bound Q (hg.sub measurable_const)
      (fun b => by
        have h := abs_add_le (g b) (-m)
        rw [← sub_eq_add_neg, abs_neg] at h
        exact h.trans (add_le_add (hMg b) le_rfl))
  have hInnerNonneg : ∀ b, 0 ≤ ∫ a, (F (a, b) - g b) ^ 2 ∂P := fun b =>
    integral_nonneg fun a => sq_nonneg _
  have hInnerBdd : ∀ b, |∫ a, (F (a, b) - g b) ^ 2 ∂P| ≤ (2 * M) ^ 2 := by
    intro b
    rw [abs_of_nonneg (hInnerNonneg b)]
    calc ∫ a, (F (a, b) - g b) ^ 2 ∂P ≤ ∫ _a, (2 * M) ^ 2 ∂P :=
          integral_mono (integrable_sq_of_bound P (hdmeas b) (hdbound b)) (integrable_const _)
            (fun a => by
              have := hdbound b a
              nlinarith [abs_nonneg (F (a, b) - g b), sq_abs (F (a, b) - g b)])
      _ = (2 * M) ^ 2 := by simp
  have hI1_sm : StronglyMeasurable (fun b => ∫ a, (F (a, b) - g b) ^ 2 ∂P) := by
    have hH : Measurable (fun p : α × β => (F p - g p.2) ^ 2) :=
      ((hF.sub (hg.comp measurable_snd)).pow_const 2)
    exact hH.stronglyMeasurable.integral_prod_left'
  have hI1 : Integrable (fun b => ∫ a, (F (a, b) - g b) ^ 2 ∂P) Q :=
    (memLp_top_of_bound hI1_sm.aestronglyMeasurable ((2 * M) ^ 2)
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]; exact hInnerBdd b)).integrable le_top
  -- assemble
  rw [hLHS]
  simp_rw [key]
  rw [integral_add hI1 hI2, hVg]
  simp_rw [hVb]

end Homogenization
