/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Conflict
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — Module C4b-1 : probability that an edge survives a
nibble round

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

The retention is now modelled as genuine independent **events** `A e` ("edge `e` is retained"),
each with probability `p` (a Bernoulli retention — stronger than the `[0,1]`-mean-`p` indicators of
C2/C3/C4a, which only recorded the mean). An edge `e` ends up in the round's matching exactly when
it is retained and none of its conflicting edges is retained. By independence, that probability
factors as `p · (1-p)^{c(e)}`, where `c(e) = |conflicts H e|`.

`conflicts` comes from `LeanPool.AsymptoticTrianglePacking.Internal.Conflict`. Must be
placeholder-free and axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- A Bernoulli retention on `H` with parameter `p`: an independent family of events `A e`
("edge `e` is retained"), each of probability `p` on the edges of `H`. -/
structure BernoulliRetention {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
    (H : Finset (Finset V)) (p : ℝ) where
  /-- The event that the edge is retained in a nibble round. -/
  A : Finset V → Set Ω
  meas : ∀ e, MeasurableSet (A e)
  indep : iIndepSet A (ℙ : Measure Ω)
  prob : ∀ e ∈ H, (ℙ : Measure Ω) (A e) = ENNReal.ofReal p

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **C4b-1 — edge survival probability.** The event that `e` is retained and none of its
conflicting edges is retained has probability `p · (1-p)^{c(e)}`. Proof: the events `A e` and the
complements `(A f)ᶜ` for `f ∈ conflicts H e` are jointly independent (all distinct, since
`conflicts H e` excludes `e`); the measure of their intersection factors as the product
`ℙ(A e) · ∏_{f} ℙ((A f)ᶜ) = p · (1-p)^{c(e)}` (each conflict `f ∈ H`, so `ρ.prob` applies, and
`ℙ((A f)ᶜ) = 1 - p`). -/
theorem edge_survives_prob {H : Finset (Finset V)} {p : ℝ} (ρ : BernoulliRetention (Ω := Ω) H p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {e : Finset V} (he : e ∈ H) :
    (ℙ : Measure Ω) (ρ.A e ∩ ⋂ f ∈ conflicts H e, (ρ.A f)ᶜ)
      = ENNReal.ofReal (p * (1 - p) ^ (conflicts H e).card) := by
  have hpe : ℙ (ρ.A e) = ENNReal.ofReal p := ρ.prob e he
  have key : ∀ f ∈ conflicts H e, f ∈ H := by
    intro f hf
    exact Finset.mem_filter.mp hf |>.1
  -- For each conflicting edge f, ℙ((A f)ᶜ) = 1 - p
  have hpcf : ∀ f ∈ conflicts H e, ℙ ((ρ.A f)ᶜ) = ENNReal.ofReal (1 - p) := by
    intro f hf
    have hmeas := ρ.meas f
    have hp := ρ.prob f (key f hf)
    rw [measure_compl hmeas, hp]
    · rw [ENNReal.sub_eq_of_eq_add ENNReal.ofReal_ne_top]
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ 1 - p) hp0]
      simp
    · exact hp ▸ ENNReal.ofReal_ne_top
  -- Define the function for independence: A e and (A f)ᶜ for conflicts
  let S := {e} ∪ conflicts H e
  let g : Finset V → Set Ω := fun f => if f = e then ρ.A e else (ρ.A f)ᶜ
  have hg_meas : ∀ f ∈ S, MeasurableSet (g f) := by
    intro f hf
    dsimp [g]
    by_cases hfe : f = e
    · rw [ite_eq_left hfe]
      exact ρ.meas e
    · rw [ite_eq_right hfe]; exact (ρ.meas f).compl
  -- The intersection ⋂ f ∈ S, g f equals our target set
  have hinter : ⋂ f ∈ S, g f = ρ.A e ∩ ⋂ f ∈ conflicts H e, (ρ.A f)ᶜ := by
    ext ω
    simp only [S, g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · intro h
      constructor
      · simpa using h e (Finset.mem_union_left _ (Finset.mem_singleton_self e))
      · intro f hf
        have hne : f ≠ e := (Finset.mem_filter.mp hf).2.1
        simpa [ite_eq_right hne] using h f (Finset.mem_union_right _ hf)
    · rintro ⟨hevent, hconf⟩ f hf
      rcases Finset.mem_union.mp hf with hfe | hcf
      · have hfe' : f = e := Finset.mem_singleton.mp hfe
        subst f
        simpa using hevent
      · have hne : f ≠ e := (Finset.mem_filter.mp hcf).2.1
        simpa [ite_eq_right hne] using hconf f hcf
  -- Use independence to factor the measure
  rw [← hinter]
  have hindeps := ρ.indep S (f := fun i => g i) (by
    intro i hi
    dsimp [g]
    by_cases hfe : i = e
    · subst i
      rw [ite_eq_left rfl]
      exact MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
    · rw [ite_eq_right hfe]
      -- Goal: MeasurableSet (ρ.A i)ᶜ in generateFrom {ρ.A i}
      exact MeasurableSet.compl (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)))
  -- Extract the equality from the a.e. statement
  rw [ae_iff] at hindeps
  have hindeps' : ℙ (⋂ i ∈ S, g i) = ∏ i ∈ S, ℙ (g i) := by
    simpa using hindeps
  rw [hindeps']
  -- Compute the product: ℙ (g e) = p and ℙ (g f) = 1 - p for f ∈ conflicts H e
  have hprod : ∏ x ∈ S, ℙ (g x) = ℙ (g e) * ∏ f ∈ conflicts H e, ℙ (g f) := by
    have hS : S = {e} ∪ conflicts H e := rfl
    rw [hS]
    rw [Finset.prod_union (by
      rw [Finset.disjoint_singleton_left]
      exact fun h => (Finset.mem_filter.mp h).2.1 rfl :
        Disjoint ({e} : Finset (Finset V)) (conflicts H e))]
    simp [g]
  rw [hprod]
  -- Compute ℙ (g e) and ℙ (g f) for f ∈ conflicts H e
  have hge : ℙ (g e) = ENNReal.ofReal p := by simpa [g] using hpe
  have hgfc : ∀ f ∈ conflicts H e, ℙ (g f) = ENNReal.ofReal (1 - p) := by
    intro f hf
    have hne : f ≠ e := (Finset.mem_filter.mp hf).2.1
    simpa [g, hne] using hpcf f hf
  rw [hge]
  rw [Finset.prod_congr rfl hgfc]
  simp only [prod_const]
  rw [← ENNReal.ofReal_pow (by linarith : 0 ≤ 1 - p)]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ p)]

end LeanPool.AsymptoticTrianglePacking.Internal
