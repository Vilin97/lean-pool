/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.MeromorphicTrace.ArgumentPrinciple
import LeanPool.JacobianDiffgeo.Meromorphic.LinearSystem

/-!
# `deg(div φ) = 0` and the unconditional `L(D) = 0` for negative degree (proper-map-degree, file 2
of 3)

Unit: proper-map-degree (`docs/design/proper-map-degree.md` §3.2). The argument principle,
repackaged from `MeromorphicTrace`'s `ℂ`-valued statement (`RS.MTrace.finsum_ordAtX_eq_zero'`,
`Jacobian/MeromorphicTrace/ArgumentPrinciple.lean`) into `ℳ X`/`Divisor` vocabulary, plus the
unconditional discharge of `Meromorphic/LinearSystem.lean`'s conditional
`linSys_eq_bot_of_degree_neg`.

**Design-doc update**: at design time `MeromorphicTrace/ArgumentPrinciple.lean` had not yet
landed, so the design's §3.2 proof plan was a ~110–150 line self-contained re-derivation of the
zeros-equal-poles finsum identity (§5 R1's documented fallback). By build time
`ArgumentPrinciple.lean` HAD landed (`finsum_ordAtX_eq_zero`/`sum_ordAtX_eq_zero_of_finite`/
`finsum_ordAtX_eq_zero'`, all complete with zero admitted gaps), so per the design's own adapter
note this file uses the "cite instead of reprove" short route: `divisor_degree_eq_zero`'s only
remaining work is (a) the
constancy case split translating `ℳ X`-nonconstancy to `MTrace.NotEventuallyConstX`, and (b)
matching `Divisor.degree`'s `Finset`-sum shape to the finsum via
`Function.locallyFinsuppWithin.degree_eq_sum_of_subset` (`Meromorphic/Divisor.lean`) — both purely
mechanical, no new mathematical content. ~60 lines total, well under the design's own "if landed"
estimate of 40–60 lines (the extra margin is the constancy-translation case split).

* `RS.divisor_degree_eq_zero` — THE argument principle in `Divisor`/`ℳ X` terms.
* `RS.sum_ord_eq_zero_of_finite` — `Finset` padding corollary.
* `RS.linSys_eq_bot_of_degree_neg'` — the unconditional discharge of
  `Meromorphic/LinearSystem.lean:206`'s conditional `linSys_eq_bot_of_degree_neg` (primed since the
  unprimed name is already taken in the same `RS` namespace by that file — cannot rename their
  declaration, `CONVENTIONS.md` rule 4).
-/

open scoped ContDiff Manifold
open Set Filter

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`deg(div φ) = 0`** for nonzero `φ : ℳ X` — the argument principle, repackaged from
`MeromorphicTrace`'s built `finsum_ordAtX_eq_zero'` into `Divisor`/CC2 terms. Consumed by
`serre-duality-tails`/`riemann-roch` (mainly via `linSys_eq_bot_of_degree_neg'` below). -/
theorem divisor_degree_eq_zero (φ : ℳ X) (hφ : φ ≠ 0) : (divisor φ).degree = 0 := by
  obtain ⟨f, hf, rfl⟩ := MeroGermOn.exists_rep φ
  by_cases hc : ∃ c : ℂ, MeroGermOn.mk f hf = algebraMap ℂ (ℳ X) c
  · obtain ⟨c, hc⟩ := hc
    rw [hc, divisor_algebraMap, Function.locallyFinsuppWithin.degree_zero]
  · push Not at hc
    have hnc : MTrace.NotEventuallyConstX f := by
      intro c hcontra
      apply hc c
      rw [MeroGermOn.algebraMap_mk]
      apply MeroGermOn.mk_eq_mk.2
      filter_upwards [hcontra] with x hx
      simp only [Pi.zero_apply] at hx
      exact sub_eq_zero.mp hx
    set S : Finset X :=
      ((divisor (MeroGermOn.mk f hf)).finiteSupport isCompact_univ).toFinset with hS_def
    have hSsub : (divisor (MeroGermOn.mk f hf)).support ⊆ (S : Set X) := by
      rw [hS_def, Set.Finite.coe_toFinset]
    rw [Function.locallyFinsuppWithin.degree_eq_sum_of_subset hSsub]
    have hpt : ∀ x ∈ S, divisor (MeroGermOn.mk f hf) x = (RS.ordAtX f x).untop₀ := by
      intro x _
      rw [divisor_apply, MeroGermOn.ord_mk isOpen_univ (mem_univ x)]
    rw [Finset.sum_congr rfl hpt]
    refine MTrace.sum_ordAtX_eq_zero_of_finite hf (MTrace.toP1_not_const hf hnc) ?_
    intro x hxne
    have hφx_ne_top : (MeroGermOn.mk f hf).ord x ≠ ⊤ := Mero.ord_ne_top hφ x
    rw [MeroGermOn.ord_mk isOpen_univ (mem_univ x)] at hφx_ne_top
    rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support, divisor_apply,
      MeroGermOn.ord_mk isOpen_univ (mem_univ x)]
    intro hcon
    rw [WithTop.untop₀_eq_zero] at hcon
    rcases hcon with hcon | hcon
    · exact hxne hcon
    · exact hφx_ne_top hcon

/-- Finset padding corollary (matches `Divisor.degree`'s definitional Finset shape). -/
theorem sum_ord_eq_zero_of_finite {φ : ℳ X} (hφ : φ ≠ 0) {s : Finset X}
    (hs : (divisor φ).support ⊆ (s : Set X)) :
    ∑ x ∈ s, divisor φ x = 0 := by
  rw [← Function.locallyFinsuppWithin.degree_eq_sum_of_subset hs]
  exact divisor_degree_eq_zero φ hφ

/-- The **unconditional** discharge of `Meromorphic.linSys_eq_bot_of_degree_neg`'s `hdeg`
hypothesis — the whole point of routing `deg(div f)=0` through this unit. -/
theorem linSys_eq_bot_of_degree_neg' (D : Divisor X) (h : D.degree < 0) :
    LinSys D = ⊥ :=
  RS.linSys_eq_bot_of_degree_neg (fun φ hφ => divisor_degree_eq_zero φ hφ) h

end RS
