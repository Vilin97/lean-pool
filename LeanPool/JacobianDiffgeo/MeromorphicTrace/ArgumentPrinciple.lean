/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: meromorphic-trace. THE argument principle, file 3 of the design's 6-file plan.
-/
import LeanPool.JacobianDiffgeo.MeromorphicTrace.OrderMultiplicity
import LeanPool.JacobianDiffgeo.MappingDegree.Degree

/-!
# The argument principle (meromorphic-trace, cluster 1)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D5, §4.3, §5 P3). Standing surface
hypotheses throughout (`[CompactSpace X] [ConnectedSpace X]` load-bearing here, unlike files 1–2).

* `finsum_ordAtX_eq_zero`: for `f` meromorphic everywhere, "nonconstant" (`toP1 f` nonconstant),
  the (finite, junk-`0`-off-support) sum of orders of `f` on compact connected `X` is `0`.
  **THE argument principle** — zeros counted with multiplicity cancel poles counted with
  multiplicity. Consumed by `proper-map-degree` for `deg(divisor f) = 0`.
* `sum_ordAtX_eq_zero_of_finite`: `Finset`-sum corollary (matches `Divisor.degree`'s shape).
* `finsum_ordAtX_eq_zero'`: convenience wrapper for callers holding the raw `f`-side nonconstancy
  hypothesis `NotEventuallyConstX` instead of `toP1`'s.

Route (§0.4 of the design): via `fiberMultSum_eq_degree` at `↑0` and `∞` on `ℙ¹` (mapping-degree's
own well-definedness engine) — **not** via the residue theorem/Stokes (deliberately, per the
design's routing warning; `proper-map-degree` needs the counting route, not a general-Stokes
route).
-/

open scoped ContDiff Manifold OnePoint
open Filter Set Function Topology

namespace RS.MTrace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {f : X → ℂ} {x : X}

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Translation lemma: `toP1 f x = ↑0` iff `f` has a genuine zero at `x` (strictly positive
order — excludes the "regular, nonvanishing" case `ordAtX f x = 0`, since an order-exactly-`0`
presentation has a *nonzero* limiting value, `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero`). -/
theorem toP1_eq_coe_zero_iff_ordAtX_pos (hf : MeromorphicOnX f Set.univ) :
    toP1 f x = ((0 : ℂ) : OnePoint ℂ) ↔ 0 < RS.ordAtX f x := by
  constructor
  · intro h
    obtain ⟨h0, hlim⟩ := toP1_eq_coe_iff.1 h
    rcases h0.eq_or_lt with heq | hlt
    · exfalso
      have heq' : meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = 0 := heq.symm
      obtain ⟨d, hdne, hd⟩ :=
        tendsto_ne_zero_of_meromorphicOrderAt_eq_zero (hf x (mem_univ x)) heq'
      have hd' : Tendsto f (𝓝[≠] x) (𝓝 d) := RS.tendsto_nhdsNE_comp_chart_iff.2 hd
      exact hdne (hd'.limUnder_eq.symm.trans hlim)
    · exact hlt
  · intro hpos
    rw [toP1_eq_coe_iff]
    refine ⟨hpos.le, ?_⟩
    have hchart : (0 : ℤ) < meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hpos
    have htend := tendsto_zero_of_meromorphicOrderAt_pos hchart
    exact (RS.tendsto_nhdsNE_comp_chart_iff.2 htend).limUnder_eq

/-- THE argument principle: the (finite, junk-`0`-off-support) sum of orders of a meromorphic,
nonconstant function on a compact connected surface is `0`. Consumed by `proper-map-degree` for
`deg(div f) = 0` (repackaging into `Divisor`/`Divisor.degree` terms is their bookkeeping). -/
theorem finsum_ordAtX_eq_zero (hf : MeromorphicOnX f Set.univ)
    (hne : ¬ ∃ c, ∀ x, toP1 f x = c) : ∑ᶠ x, (RS.ordAtX f x).untop₀ = 0 := by
  classical
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toP1 f) := toP1_contMDiff hf
  have hdeg0 : RS.fiberMultSum (toP1 f) ((0 : ℂ) : OnePoint ℂ) = RS.degree (toP1 f) :=
    RS.fiberMultSum_eq_degree hF hne _
  have hdeginf : RS.fiberMultSum (toP1 f) (∞ : OnePoint ℂ) = RS.degree (toP1 f) :=
    RS.fiberMultSum_eq_degree hF hne _
  have hfin0 := RS.fiber_finite hF hne ((0 : ℂ) : OnePoint ℂ)
  have hfininf := RS.fiber_finite hF hne (∞ : OnePoint ℂ)
  have heq0 : RS.fiberMultSum (toP1 f) ((0 : ℂ) : OnePoint ℂ) =
      ∑ x ∈ hfin0.toFinset, RS.multiplicity (toP1 f) x := RS.fiberMultSum_eq_finset_sum hfin0
  have heqinf : RS.fiberMultSum (toP1 f) (∞ : OnePoint ℂ) =
      ∑ x ∈ hfininf.toFinset, RS.multiplicity (toP1 f) x := RS.fiberMultSum_eq_finset_sum hfininf
  have hmain : (∑ x ∈ hfin0.toFinset, (RS.multiplicity (toP1 f) x : ℤ)) =
      ∑ x ∈ hfininf.toFinset, (RS.multiplicity (toP1 f) x : ℤ) := by
    have h1 : RS.fiberMultSum (toP1 f) ((0 : ℂ) : OnePoint ℂ) =
        RS.fiberMultSum (toP1 f) (∞ : OnePoint ℂ) := hdeg0.trans hdeginf.symm
    rw [heq0, heqinf] at h1
    exact_mod_cast h1
  have hterm0 : ∀ x ∈ hfin0.toFinset, (RS.multiplicity (toP1 f) x : ℤ) =
      (RS.ordAtX f x).untop₀ := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact multiplicity_toP1_of_ordAtX_pos hf ((toP1_eq_coe_zero_iff_ordAtX_pos hf).1 hx)
  have hterminf : ∀ x ∈ hfininf.toFinset, (RS.multiplicity (toP1 f) x : ℤ) =
      -(RS.ordAtX f x).untop₀ := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact multiplicity_toP1_of_ordAtX_neg hf (toP1_eq_infty_iff.1 hx)
  rw [Finset.sum_congr rfl hterm0, Finset.sum_congr rfl hterminf] at hmain
  -- `hmain : ∑ x ∈ s₀, ord.untop₀ = ∑ x ∈ s∞, -ord.untop₀`; the two Finsets are disjoint
  -- (order can't be both `> 0` and `< 0`), so `∑ x ∈ s₀ ∪ s∞, ord.untop₀ = 0`.
  have hdisj : Disjoint hfin0.toFinset hfininf.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx0 hxinf
    rw [Set.Finite.mem_toFinset] at hx0 hxinf
    have h1 : 0 < RS.ordAtX f x := (toP1_eq_coe_zero_iff_ordAtX_pos hf).1 hx0
    have h2 : RS.ordAtX f x < 0 := toP1_eq_infty_iff.1 hxinf
    exact absurd (h1.trans h2) (lt_irrefl _)
  have hsupp : Function.support (fun x => (RS.ordAtX f x).untop₀) ⊆
      ↑(hfin0.toFinset ∪ hfininf.toFinset) := by
    intro x hx
    simp only [Function.mem_support] at hx
    rw [Finset.coe_union, Set.mem_union]
    rcases lt_trichotomy (RS.ordAtX f x) 0 with hlt | heq | hgt
    · right; simp only [Finset.mem_coe, Set.Finite.mem_toFinset]; exact toP1_eq_infty_iff.2 hlt
    · exact absurd (by simp [heq]) hx
    · left; simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact (toP1_eq_coe_zero_iff_ordAtX_pos hf).2 hgt
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_union hdisj]
  rw [Finset.sum_neg_distrib] at hmain
  linarith

/-- `Finset` form (matches `Divisor.degree`'s `Finset.sum`-over-`finiteSupport` shape) — a
trivial corollary padding the finsum to any `Finset` containing the support. -/
theorem sum_ordAtX_eq_zero_of_finite {s : Finset X}
    (hf : MeromorphicOnX f Set.univ) (hne : ¬ ∃ c, ∀ x, toP1 f x = c)
    (hs : ∀ x, RS.ordAtX f x ≠ 0 → x ∈ s) :
    ∑ x ∈ s, (RS.ordAtX f x).untop₀ = 0 := by
  rw [← finsum_ordAtX_eq_zero hf hne]
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro x hx
  simp only [Function.mem_support] at hx
  exact hs x (fun h => hx (by simp [h]))

/-- Convenience packaging for callers holding the raw `f`-side nonconstancy hypothesis
`NotEventuallyConstX` instead of `toP1`'s (D3's translation, `toP1_not_const`). -/
theorem finsum_ordAtX_eq_zero' (hf : MeromorphicOnX f Set.univ) (hnc : NotEventuallyConstX f) :
    ∑ᶠ x, (RS.ordAtX f x).untop₀ = 0 :=
  finsum_ordAtX_eq_zero hf (toP1_not_const hf hnc)

end RS.MTrace
