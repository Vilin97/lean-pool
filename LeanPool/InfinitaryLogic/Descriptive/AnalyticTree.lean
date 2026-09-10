/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.QueryCode
/-!
# The analytic tree normal form (issue #10, Unit 0b)

The second half of the López–Escobar stop/go gate (audit v2, D3): every analytic subset of
the structure space is the branch projection of a cylinder tree in `(ℕ → Bool) × (ℕ → ℕ)`,
through the query-code closed embedding —

`c ∈ B ↔ ∃ g : ℕ → ℕ, ∀ n, (prefix (queryCode c) n, prefix g n) ∈ T n`.

Mathlib's `MeasureTheory.AnalyticSet` is the continuous-image form (`∅` or a continuous
image of Baire space); the tree at level `n` is simply the set of length-`n` prefixes of
graph points of the composed witness `queryCode ∘ f`, so the forward direction is the graph
point itself and the converse chooses **one graph point per prefix** and passes to the
coordinatewise limit: each coordinate is eventually fixed once the prefix length passes its
index, so the chosen points converge to `(queryCode c, g)`, continuity gives
`queryCode (f g) = queryCode c`, and injectivity of the query code finishes.  The empty
analytic set is served by the branchless tree.
-/

namespace FirstOrder.Language

open Set Filter

variable {L : Language.{u, v}} [Countable (Σ l, L.Relations l)]

/-- **The analytic tree normal form** (audit v2, D3 — the stop/go gate): an analytic class
of coded structures is the branch projection of a level-indexed cylinder tree along the
query code. -/
theorem exists_tree_of_analyticSet {B : Set (StructureSpace L)}
    (hB : MeasureTheory.AnalyticSet B) :
    ∃ T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)),
      ∀ c, c ∈ B ↔ ∃ g : ℕ → ℕ,
        ∀ n, ((fun i : Fin n => queryCode c i), (fun i : Fin n => g i)) ∈ T n := by
  rw [MeasureTheory.AnalyticSet] at hB
  rcases hB with rfl | ⟨f, hf, rfl⟩
  · -- the empty set: the branchless tree
    refine ⟨fun _ => ∅, fun c => ?_⟩
    constructor
    · rintro ⟨⟩
    · rintro ⟨g, hg⟩
      exact hg 0
  · -- B = range f: the tree of length-n prefixes of graph points of queryCode ∘ f
    refine ⟨fun n => Set.range (fun y : ℕ → ℕ =>
      ((fun i : Fin n => queryCode (f y) i), (fun i : Fin n => y i))), fun c => ?_⟩
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, fun n => ⟨y, rfl⟩⟩
    · rintro ⟨g, hg⟩
      choose w hw using hg
      -- the chosen witnesses converge to g coordinatewise (eventually constant)
      have hwg : Tendsto w atTop (nhds g) := by
        rw [tendsto_pi_nhds]
        intro i
        refine tendsto_atTop_of_eventually_const (i₀ := i + 1) fun n hn => ?_
        exact congrFun (congrArg Prod.snd (hw n)) ⟨i, by omega⟩
      have hFg : Tendsto (fun n => queryCode (f (w n))) atTop (nhds (queryCode (f g))) :=
        ((continuous_queryCode.comp hf).tendsto g).comp hwg
      -- each query-code coordinate of the witnesses is eventually the target coordinate
      have hcoord : ∀ k, queryCode (f g) k = queryCode c k := by
        intro k
        have h1 : Tendsto (fun n => queryCode (f (w n)) k) atTop
            (nhds (queryCode (f g) k)) := (tendsto_pi_nhds.mp hFg) k
        have h2 : Tendsto (fun n => queryCode (f (w n)) k) atTop
            (nhds (queryCode c k)) := by
          refine tendsto_atTop_of_eventually_const (i₀ := k + 1) fun n hn => ?_
          exact congrFun (congrArg Prod.fst (hw n)) ⟨k, by omega⟩
        exact tendsto_nhds_unique h1 h2
      have hcodes : queryCode (f g) = queryCode c := funext hcoord
      exact queryCode_injective hcodes ▸ Set.mem_range_self g

end FirstOrder.Language
