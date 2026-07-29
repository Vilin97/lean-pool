/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.AuxiliaryFunction

/-!
# Admissible test functions for the Weil–Poitou explicit formula  (T-ADM, T-BV)

Belabas–Friedman state Weil's explicit formula (their eq. (1), Poitou's form) for an
auxiliary function `F : ℝ → ℂ` subject to the hypotheses on p. 3, verbatim:

* "`F` is assumed to be even";
* "for some `ε > 0`, the function `F(x)e^{(1/2+ε)x}` is of bounded variation and
  integrable over `[0,+∞)`";
* "`(F(0) − F(x))/x` is assumed of bounded variation on `[0,+∞)`";
* "`F` must be assigned the average value at any jump discontinuity".

`IsAdmissibleTestFn` bundles exactly these four conditions, so the explicit formula
(SP2) and its applications (Lemma 3) quote one hypothesis instead of four.

The bounded-variation side conditions are discharged for concrete test functions
(the paper's `F_{s,X}`, which is continuous and piecewise `C¹` with a kink at
`|t| = log X`) through the T-BV lemmas proved here:

* `eVariationOn_le_integral_norm_deriv` — on an order-connected set, the total
  variation of a continuous function with integrable derivative on the interior is
  at most `∫ ‖f′‖`;
* `boundedVariationOn_of_deriv_integrable` — the resulting finiteness;
* `boundedVariationOn_Ici_of_piecewise_deriv` — the two-piece glue for a kink at
  `b`: continuous on `[a,∞)`, `C¹` on `(a,b)` and `(b,∞)`, derivative integrable.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory
open scoped Real

/-- **Admissibility for the Weil–Poitou explicit formula** (Belabas–Friedman, p. 3,
verbatim hypotheses on the auxiliary function): `F` is even; for some `ε > 0` the
function `F(x)e^{(1/2+ε)x}` is of bounded variation and integrable over `[0,∞)`;
`(F(0)-F(x))/x` is of bounded variation on `[0,∞)`; and `F` takes the average of its
one-sided limits everywhere (the "average value at any jump discontinuity" convention —
at continuity points the condition holds trivially with `L = R = F x`). -/
structure IsAdmissibleTestFn (F : ℝ → ℂ) : Prop where
  even : ∀ x : ℝ, F (-x) = F x
  bv_integrable_exp : ∃ ε : ℝ, 0 < ε
    ∧ BoundedVariationOn (fun x : ℝ => F x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
        (Set.Ici 0)
    ∧ IntegrableOn (fun x : ℝ => F x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
        (Set.Ici 0)
  diffQuot_bv : BoundedVariationOn (fun x : ℝ => (F 0 - F x) / x) (Set.Ici 0)
  jump_avg : ∀ x : ℝ, ∃ L R : ℂ,
    Filter.Tendsto F (nhdsWithin x (Set.Iio x)) (nhds L)
    ∧ Filter.Tendsto F (nhdsWithin x (Set.Ioi x)) (nhds R)
    ∧ F x = (L + R) / 2

/-- **T-BV workhorse**: on an order-connected set `s`, a function continuous on `s`
with derivative `f'` on the interior has total variation at most `∫_s ‖f'‖`.
(Each partition increment is `‖∫ f'‖ ≤ ∫ ‖f'‖` by the fundamental theorem of calculus;
adjacent segments chain into one interval inside `s`.) -/
theorem eVariationOn_le_integral_norm_deriv {f f' : ℝ → ℂ} {s : Set ℝ}
    (hs : s.OrdConnected) (hcont : ContinuousOn f s)
    (hderiv : ∀ x ∈ interior s, HasDerivAt f (f' x) x)
    (hint : IntegrableOn f' s) :
    eVariationOn f s ≤ ENNReal.ofReal (∫ x in s, ‖f' x‖) := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  -- each segment [u i, u (i+1)] lies in s, and FTC applies on it
  have hIcc : ∀ i : ℕ, Set.Icc (u i) (u (i + 1)) ⊆ s :=
    fun i => hs.out (us i) (us (i + 1))
  have hii : ∀ i : ℕ, IntervalIntegrable f' volume (u i) (u (i + 1)) := by
    intro i
    have := hint.mono_set (hIcc i)
    rw [← Set.uIcc_of_le (hu (Nat.le_succ i))] at this
    exact this.intervalIntegrable
  have hiin : ∀ i : ℕ, IntervalIntegrable (fun x => ‖f' x‖) volume (u i) (u (i + 1)) :=
    fun i => (hii i).norm
  have hseg : ∀ i : ℕ, f (u (i + 1)) - f (u i) = ∫ y in (u i)..(u (i + 1)), f' y := by
    intro i
    have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hIoo : Set.Ioo (u i) (u (i + 1)) ⊆ interior s :=
      interior_maximal ((Set.Ioo_subset_Icc_self).trans (hIcc i)) isOpen_Ioo
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hle
      (hcont.mono (hIcc i)) (fun x hx => (hderiv x (hIoo hx)).hasDerivWithinAt)
      (hii i)]
  -- real-valued chain: ∑ ‖increments‖ ≤ ∫_s ‖f'‖
  have hreal : (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖)
      ≤ ∫ x in s, ‖f' x‖ := by
    have hstep : ∀ i ∈ Finset.range n,
        ‖f (u (i + 1)) - f (u i)‖ ≤ ∫ y in (u i)..(u (i + 1)), ‖f' y‖ := by
      intro i _
      rw [hseg i]
      exact intervalIntegral.norm_integral_le_integral_norm (hu (Nat.le_succ i))
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hiin k),
      intervalIntegral.integral_of_le (hu (Nat.zero_le n))]
    refine setIntegral_mono_set hint.norm
      (Filter.Eventually.of_forall (fun x => norm_nonneg _)) ?_
    exact ((Set.Ioc_subset_Icc_self).trans (hs.out (us 0) (us n))).eventuallyLE
  calc (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
      = ∑ i ∈ Finset.range n, ENNReal.ofReal ‖f (u (i + 1)) - f (u i)‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [edist_dist, dist_eq_norm]
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)).symm
    _ ≤ ENNReal.ofReal (∫ x in s, ‖f' x‖) := ENNReal.ofReal_le_ofReal hreal

/-- A function continuous on an order-connected set with integrable derivative on the
interior has bounded variation there. -/
theorem boundedVariationOn_of_deriv_integrable {f f' : ℝ → ℂ} {s : Set ℝ}
    (hs : s.OrdConnected) (hcont : ContinuousOn f s)
    (hderiv : ∀ x ∈ interior s, HasDerivAt f (f' x) x)
    (hint : IntegrableOn f' s) :
    BoundedVariationOn f s :=
  ((eVariationOn_le_integral_norm_deriv hs hcont hderiv hint).trans_lt
    ENNReal.ofReal_lt_top).ne

/-- **T-BV, piecewise form**: a function continuous on `[a,∞)`, differentiable off a
single kink at `b` (with `a ≤ b`), whose derivative is integrable on `[a,∞)`, has
bounded variation on `[a,∞)`. This is the shape the paper's `F_{s,X}` (kink at
`t = log X`) discharges. -/
theorem boundedVariationOn_Ici_of_piecewise_deriv {f f' : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Set.Ici a))
    (hd1 : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ Set.Ioi b, HasDerivAt f (f' x) x)
    (hint : IntegrableOn f' (Set.Ici a)) :
    BoundedVariationOn f (Set.Ici a) := by
  have h1 : BoundedVariationOn f (Set.Icc a b) :=
    boundedVariationOn_of_deriv_integrable Set.ordConnected_Icc
      (hcont.mono Set.Icc_subset_Ici_self)
      (by rwa [interior_Icc])
      (hint.mono_set Set.Icc_subset_Ici_self)
  have h2 : BoundedVariationOn f (Set.Ici b) :=
    boundedVariationOn_of_deriv_integrable Set.ordConnected_Ici
      (hcont.mono (Set.Ici_subset_Ici.mpr hab))
      (by rwa [interior_Ici])
      (hint.mono_set (Set.Ici_subset_Ici.mpr hab))
  have hunion : Set.Ici a = Set.Icc a b ∪ Set.Ici b :=
    (Set.Icc_union_Ici_eq_Ici hab).symm
  unfold BoundedVariationOn at h1 h2 ⊢
  rw [hunion, eVariationOn.union f
    ⟨Set.right_mem_Icc.mpr hab, fun x hx => hx.2⟩
    ⟨Set.self_mem_Ici, fun x hx => hx⟩]
  exact ENNReal.add_ne_top.mpr ⟨h1, h2⟩

end

end DedekindResidue
