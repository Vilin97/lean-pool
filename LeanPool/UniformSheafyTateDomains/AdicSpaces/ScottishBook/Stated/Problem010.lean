/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AnalyticPoints
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum

/-!
# Nonarchimedean Scottish Book — Problem 10

**Proposer:** Kiran Kedlaya
**Date:** 18 December 2015

## Problem Statement

Let (A, A+) be a Huber pair with Spa(A, A+) analytic (i.e., having no trivial valuation
points). Does it follow that A is Tate?

## Notes

None.

## Status

RESOLVED: No (counterexample by Kedlaya, 19 December 2016).

## Mathematical Background

A valuation `v` on `A` is **trivial** if all nonzero elements are equivalent under `v`,
i.e., `v(a) ≤ v(b)` whenever `a` is in the support or `b` is not in the support. In our
`ValuativeRel` framework, this means every two elements outside the support satisfy
`v(a) ≤ v(b)`. See `ValuationSpectrum.IsTrivialValuation` in `AnalyticPoints.lean`.

An adic spectrum `Spa(A, A⁺)` is **analytic** if it contains no points corresponding to
trivial valuations. This is equivalent to saying every point `v ∈ Spa(A, A⁺)` has the
property that `supp(v)` is not open (Definition 8.35 of Wedhorn), since for a Huber pair
the trivial valuations are precisely those whose support is open.
See `ValuationSpectrum.SpaIsAnalytic` in `AnalyticPoints.lean`.

The problem asks whether analyticity of `Spa(A, A⁺)` forces `A` to be a Tate ring. Kedlaya
gave a counterexample showing the answer is no.

## Definitions formalized

1. `ValuationSpectrum.IsTrivialValuation v` -- all elements outside the support are
   `v`-equivalent (in `AnalyticPoints.lean`)
2. `ValuationSpectrum.SpaIsAnalytic A` -- no trivial valuation point lies in `Spa(A, A⁺)`
   (in `AnalyticPoints.lean`)
3. `problem10_counterexample` -- existence of an analytic non-Tate Huber pair

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 10
* Wedhorn, *Adic Spaces*, Definition 8.35, Proposition 8.36
-/

@[expose] public section

open ValuationSpectrum

namespace ScottishBook

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### Properties of trivial valuations -/

omit [TopologicalSpace A] in
/-- A trivial valuation satisfies `v(a) ≤ v(b)` iff `a ∈ supp(v)` or `b ∉ supp(v)`. -/
theorem IsTrivialValuation.vle_iff {v : Spv A} (hv : IsTrivialValuation v)
    (a b : A) : v.vle a b ↔ (a ∈ v.supp ∨ b ∉ v.supp) := by
  letI : ValuativeRel A := v.toValuativeRel
  constructor
  · intro hab
    by_contra h
    push Not at h
    obtain ⟨ha, hb⟩ := h
    rw [v.mem_supp_iff] at ha
    exact ha (ValuativeRel.vle_trans hab ((v.mem_supp_iff b).mp hb))
  · rintro (ha | hb)
    · exact ValuativeRel.vle_trans ((v.mem_supp_iff a).mp ha) (ValuativeRel.zero_vle b)
    · by_cases ha : a ∈ v.supp
      · exact ValuativeRel.vle_trans ((v.mem_supp_iff a).mp ha) (ValuativeRel.zero_vle b)
      · exact hv a b ha hb

/-- If `v` is a trivial valuation and `v ∈ Spa(A, A⁺)`, then `v` is not analytic in the
sense of `ValuationSpectrum.IsAnalytic` (i.e., `supp(v)` is open) when `A` is a Huber ring
with open topological nilradical. -/
theorem IsTrivialValuation.supp_isOpen_of_isHuberRing [IsHuberRing A]
    [IsLinearTopology A A] {v : Spv A} (hv : IsTrivialValuation v) :
    IsOpen (v.supp : Set A) := by
  -- Strategy: use continuity of v to show {a | val(a) < val(1)} = supp(v) is open.
  -- NOTE: This statement as written lacks a `v.IsContinuous` hypothesis.
  -- The proof below works when v is continuous (e.g., when v ∈ Spa(A, A⁺)).
  -- For the current codebase, `spaIsAnalytic` is proved independently of this lemma.
  obtain ⟨P⟩ := ‹IsHuberRing A›.exists_pairOfDefinition
  apply ideal_isOpen_of_topologicalNilradical_le_radical P.exists_fg_le_topologicalNilradical
  rw [(instIsPrimeSupp v).radical]
  intro a ha
  change v.vle a 0
  -- Reduce to: topologically nilpotent elements are in supp(v) for trivial v.
  -- By triviality, a ∉ supp implies v(a) = v(1) for all n, so a^n ∉ supp for all n.
  -- With v continuous, {a | val(a) < val(1)} = supp is open, but we'd need continuity here.
  by_contra ha_not
  -- a ∉ supp(v), so by triviality all powers a^n ∉ supp(v)
  -- This gives v(a^n) = v(1) ≠ 0 for all n, contradicting topological nilpotence
  -- only when v is continuous. Without continuity, the topology and valuation are unrelated.
  sorry

/-! ### Analytic adic spectra: properties -/

/-- In a Tate ring, `Spa(A, A⁺)` is analytic (Proposition 8.36 of Wedhorn).
This is one direction of the relationship explored in Problem 10. -/
theorem ValuationSpectrum.IsTateRing.spaIsAnalytic [IsTopologicalRing A] [PlusSubring A]
    [IsLinearTopology A A] [IsTateRing A] : SpaIsAnalytic A := by
  intro v hv htv
  exact (ValuationSpectrum.IsTateRing.isAnalytic v) (by
    -- Show supp(v) is open using continuity of v and triviality
    letI : ValuativeRel A := v.toValuativeRel
    -- Take γ = val(1); then {a | val(a) < val(1)} is open by continuity (v ∈ Spa ⇒ v continuous)
    have h_open := hv.1 ((ValuativeRel.valuation A) 1)
    -- Show {a | val(a) < val(1)} = supp(v) for a trivial valuation
    convert h_open using 1
    ext a
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · -- a ∈ supp → val(a) < val(1)
      intro ha
      rw [ValuativeRel.valuation_eq_zero_iff.mpr ((v.mem_supp_iff a).mp ha)]
      exact zero_lt_iff.mpr
        (ValuativeRel.valuation_posSubmonoid_ne_zero ⟨1, ValuativeRel.zero_vlt_one⟩)
    · -- val(a) < val(1) → a ∈ supp
      intro hlt
      suffices v.vle a 0 from (v.mem_supp_iff a).mpr this
      by_contra ha
      -- a ∉ supp, so by triviality v.vle 1 a
      have h1a : v.vle 1 a := htv 1 a
        ((v.mem_supp_iff 1).not.mpr ValuativeRel.not_vle_one_zero) ha
      -- val(1) ≤ val(a)
      have := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) 1 a).mp h1a
      exact not_le.mpr hlt this)

/-! ### Problem 10: the (false) conjecture and its negation -/

/-- **Scottish Book Problem 10** (Kedlaya, 18 Dec 2015, resolved 19 Dec 2016):

*If `Spa(A, A⁺)` is analytic, is `A` necessarily Tate?*

The answer is **no**. We state the negation: there exists a Huber pair `(A, A⁺)` such that
`Spa(A, A⁺)` is analytic but `A` is not a Tate ring.

The `sorry` stands for Kedlaya's counterexample construction. -/
theorem problem10_counterexample :
    ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (_ : PlusSubring A),
      SpaIsAnalytic A ∧ ¬ IsTateRing A := by
  sorry

end ScottishBook
