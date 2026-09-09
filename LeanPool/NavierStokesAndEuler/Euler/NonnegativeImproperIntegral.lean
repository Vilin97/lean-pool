/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Unbounded finite partial integrals of a nonnegative function force
its extended integral on the half-open interval to be infinite. Local
integrability is explicit, so no totalized real integral is used as a
substitute for an improper integral. -/

noncomputable section

namespace EulerNonnegativeImproperIntegral

open Set MeasureTheory
open scoped ENNReal

theorem ofReal_partial_le_lintegral (f : ℝ → ℝ) {S T : ℝ}
    (hS : 0 ≤ S) (hST : S < T) (hf : IntervalIntegrable f volume 0 S)
    (hnonneg : ∀ x ∈ Ioc (0 : ℝ) S, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in (0 : ℝ)..S, f x) ≤
      ∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hS,
    ofReal_integral_eq_lintegral_ofReal hf.1
      (ae_restrict_of_forall_mem measurableSet_Ioc hnonneg)]
  exact lintegral_mono_set (fun _ hx => ⟨hx.1.le,hx.2.trans_lt hST⟩)

theorem lintegral_eq_top_of_unbounded_partials (f : ℝ → ℝ) (T : ℝ)
    (hf : ∀ S : ℝ, 0 < S → S < T → IntervalIntegrable f volume 0 S)
    (hnonneg : ∀ x ∈ Ico (0 : ℝ) T, 0 ≤ f x)
    (hunbounded : ∀ K : ℝ, ∃ S : ℝ, 0 < S ∧ S < T ∧
      K < ∫ x in (0 : ℝ)..S, f x) :
    (∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x))=⊤ := by
  by_contra hfinite
  obtain ⟨S,hS,hST,hK⟩ := hunbounded
    (∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x)).toReal
  have hb := ofReal_partial_le_lintegral f hS.le hST (hf S hS hST)
    (fun x hx => hnonneg x ⟨hx.1.le,hx.2.trans_lt hST⟩)
  exact (not_lt_of_ge hb) ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hK)

end EulerNonnegativeImproperIntegral
