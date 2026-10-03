/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the AX1 structural residual in its **local** design form

`Nibble.CoreGapGridResidual` records the AX1 residual as `Nibble.AX1.SubTripleDesignResidual`, the
existence of a `Nibble.AX1.IsSubTripleDesign`.  That package charges the exceptional edges of the
`i`-th sub-triple at the *global* rate `(2·Badᵢ/t)·|V|`.  As explained in
`Nibble.CoreGapDesignLocal`, that global rate cannot be met by any construction whose sub-triples
live inside the clusters of the regularity partition:

* the sub-triples are `ε₂`-uniform only because they are blocks of relative size `α` inside an
  `(ε₁/8)`-uniform cluster pair, so `ε₂ ≥ ε₁/(8α)`;
* their triangle-degree scale `d` is at most the size of a cluster, `≈ |V|/m`, so the slack `t`
  obeys `t ≤ μ·|V|/m` with `m = #P.parts`;
* the exceptional clause then forces `ε₂ ≲ ημδ/m`, i.e. `ε₁·m ≲ ημ·α`, while the hypotheses of
  `Nibble.AX1.SubTripleDesignAt` themselves force `m ≥ 4/ε₁`, hence `ε₁ · m ≥ 4`.

So for small `η` or `μ` the *global* design form is out of reach of the grid construction — and the
project already carries the repair: `Nibble.AX1.hasNearRegularFamily_of_subTripleDesignLocal`
(`Nibble.CoreGapDesignLocal`) provides exactly the same bridge with the exceptional edges charged
against the *support* `|A| + |B| + |C|` of the sub-triple, which is the honest rate coming out of
`Nibble.AX1.uniform_triple_member_local`.

This file mirrors `Nibble.CoreGapGridResidual` for that local bridge:

* `Nibble.AX1.SubTripleDesignLocalAt`, `Nibble.AX1.SubTripleDesignLocalResidual` — the residual in
  local design form;
* `Nibble.AX1.reducedFamilyAt_of_subTripleDesignLocalAt`,
  `Nibble.AX1.reducedFamilyResidual_of_subTripleDesignLocal`,
  `Nibble.AX1.ax1_of_subTripleDesignLocal` — the machine-checked reductions to
  `Nibble.AX1.ReducedFamilyAt`, `Nibble.AX1.ReducedFamilyResidual` and `AX1Statement`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapTripleShape
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPrune



/-! # CoreGapPruneLocal -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Few edges have an endpoint at which many edges were deleted — localised version.**  The
number of vertices at which more than `t` edges were deleted is at most `2|Bad|/t`, and each of them
lies in at most `D` edges. -/
theorem card_edges_heavy_deleted_le_of_degree (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {t : ℝ} (ht : 0 < t) {D : ℕ}
    (hdeg : ∀ v : V, #{z ∈ (univ : Finset V) | T.Adj v z} ≤ D) :
    ((#{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)} : ℕ) : ℝ)
      ≤ (2 * (#Bad : ℝ) / t) * (D : ℝ) := by
  classical
  set S : Finset V := {v ∈ (univ : Finset V) | t < (deletedDegree T Bad v : ℝ)} with hS
  have hsub : {e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)}
      ⊆ S.biUnion (fun v => {z ∈ (univ : Finset V) | T.Adj v z}.image
        (fun z => ({v, z} : Finset V))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hecl, hbad⟩ := he
    push Not at hbad
    obtain ⟨v, hve, hvt⟩ := hbad
    have hvS : v ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ v, hvt⟩
    have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp hecl).card_eq
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have hadj : T.Adj a b := (pair_mem_cliqueFinset_two T hab).mp hecl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hve
    refine Finset.mem_biUnion.mpr ⟨v, hvS, ?_⟩
    rcases hve with rfl | rfl
    · exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hadj⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hadj.symm⟩,
        Finset.pair_comm v a⟩
  have hcard1 : #{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)}
      ≤ ∑ _v ∈ S, D := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    exact Finset.sum_le_sum fun v _ => le_trans Finset.card_image_le (hdeg v)
  have hcard2 : ((#{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)} : ℕ) : ℝ)
      ≤ (#S : ℝ) * (D : ℝ) := by
    have h := hcard1
    rw [Finset.sum_const, smul_eq_mul] at h
    exact_mod_cast h
  have hmark := card_vertices_deletedDegree_gt T Bad (t := t)
  have hSt : (#S : ℝ) ≤ 2 * (#Bad : ℝ) / t := by
    rw [le_div_iff₀ ht]
    exact hmark
  exact le_trans hcard2 (mul_le_mul_of_nonneg_right hSt (by positivity))

/-- **The pruned graph — localised.**  As `Nibble.AX1.prune_near_regular`, but the exceptional set
is bounded using a degree bound `D` for `T` instead of the number of vertices of the ambient
graph. -/
theorem prune_near_regular_local (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {μ d t : ℝ} (ht : 0 < t) {D : ℕ}
    (hdeg : ∀ v : V, #{z ∈ (univ : Finset V) | T.Adj v z} ≤ D)
    (hhi : ∀ e ∈ T.cliqueFinset 2, e ∉ Bad → (edgeTriangleDegree T e : ℝ) ≤ (1 + μ) * d)
    (hlo : ∀ e ∈ T.cliqueFinset 2, e ∉ Bad → (1 - μ) * d ≤ (edgeTriangleDegree T e : ℝ)) :
    (∀ e ∈ (prune T Bad).cliqueFinset 2,
        (edgeTriangleDegree (prune T Bad) e : ℝ) ≤ (1 + μ) * d) ∧
      ∃ Exc : Finset (Finset V), ((#Exc : ℕ) : ℝ) ≤ (2 * (#Bad : ℝ) / t) * (D : ℝ) ∧
        ∀ e ∈ (prune T Bad).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d - 2 * t ≤ (edgeTriangleDegree (prune T Bad) e : ℝ) := by
  classical
  refine ⟨(prune_near_regular T Bad ht hhi hlo).1, ?_⟩
  refine ⟨{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)},
    card_edges_heavy_deleted_le_of_degree T Bad ht hdeg, ?_⟩
  intro e he hexc
  obtain ⟨heT, heB⟩ := mem_cliqueFinset_two_prune T Bad he
  have hdeg' : ∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t := by
    by_contra hc
    exact hexc (Finset.mem_filter.mpr ⟨heT, hc⟩)
  have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have hadj : (prune T Bad).Adj x y := (pair_mem_cliqueFinset_two _ hxy).mp he
  have hdrop := edgeTriangleDegree_prune_ge T Bad hadj
  have hdrop' : ((edgeTriangleDegree T {x, y} : ℕ) : ℝ)
      ≤ ((edgeTriangleDegree (prune T Bad) {x, y} : ℕ) : ℝ)
        + ((deletedDegree T Bad x : ℕ) : ℝ) + ((deletedDegree T Bad y : ℕ) : ℝ) := by
    exact_mod_cast hdrop
  have hx : ((deletedDegree T Bad x : ℕ) : ℝ) ≤ t := hdeg' x (by simp)
  have hy : ((deletedDegree T Bad y : ℕ) : ℝ) ≤ t := hdeg' y (by simp)
  have hlo' := hlo {x, y} heT heB
  linarith only [hdrop', hx, hy, hlo']

omit [DecidableEq V] in
/-- **A tripartite graph has degrees at most `|U| + |W| + |X|`**: all its edges stay inside the
three parts. -/
theorem tripleGraph_degree_le (G : SimpleGraph V) (U W X : Finset V) (v : V) :
    #{z ∈ (univ : Finset V) | (tripleGraph G U W X).Adj v z} ≤ #U + #W + #X := by
  classical
  have hsub : {z ∈ (univ : Finset V) | (tripleGraph G U W X).Adj v z} ⊆ U ∪ W ∪ X := by
    intro z hz
    rw [Finset.mem_filter] at hz
    have hcross := hz.2.2
    unfold crossAdj at hcross
    simp only [Finset.mem_union]
    tauto
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- **A near-regular member of the family from one cluster triple — localised.**  As
`Nibble.AX1.uniform_triple_member`, but the exceptional edges are bounded by
`(2|Bad|/t)·(|U| + |W| + |X|)`, which involves only the triple and not the ambient graph. -/
theorem uniform_triple_member_local (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X) {ε μ d t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hUWu : G.IsUniform ε U W) (hUXu : G.IsUniform ε U X) (hWXu : G.IsUniform ε W X)
    (hdUW : 2 * ε ≤ (G.edgeDensity U W : ℝ)) (hdUX : 2 * ε ≤ (G.edgeDensity U X : ℝ))
    (hdWX : 2 * ε ≤ (G.edgeDensity W X : ℝ))
    (hXlo : (1 - μ) * d ≤ ((G.edgeDensity U X : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#X : ℝ))
    (hXhi : ((G.edgeDensity U X : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#X : ℝ)
      ≤ (1 + μ) * d)
    (hWlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#W : ℝ))
    (hWhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#W : ℝ)
      ≤ (1 + μ) * d)
    (hUlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity U X : ℝ) - 2 * ε)
      * (#U : ℝ))
    (hUhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity U X : ℝ) + 2 * ε) * (#U : ℝ)
      ≤ (1 + μ) * d) :
    ∃ Bad : Finset (Finset V),
      ((#Bad : ℕ) : ℝ) ≤ 4 * ε * ((#U : ℝ) * (#W : ℝ) + (#U : ℝ) * (#X : ℝ)
        + (#W : ℝ) * (#X : ℝ)) ∧
      prune (tripleGraph G U W X) Bad ≤ G ∧
      (∀ e ∈ (prune (tripleGraph G U W X) Bad).cliqueFinset 2,
        (edgeTriangleDegree (prune (tripleGraph G U W X) Bad) e : ℝ) ≤ (1 + μ) * d) ∧
      (∃ Exc : Finset (Finset V),
        ((#Exc : ℕ) : ℝ) ≤ (2 * ((#Bad : ℕ) : ℝ) / t) * ((#U : ℝ) + (#W : ℝ) + (#X : ℝ)) ∧
        ∀ e ∈ (prune (tripleGraph G U W X) Bad).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d - 2 * t
            ≤ (edgeTriangleDegree (prune (tripleGraph G U W X) Bad) e : ℝ)) ∧
      ((#((tripleGraph G U W X).cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
        ≤ ((#((prune (tripleGraph G U W X) Bad).cliqueFinset 2) : ℕ) : ℝ) := by
  classical
  obtain ⟨Bad, hBadcard, hBad⟩ := tripleGraph_near_regular G hUW hUX hWX hε hε1 hUWu hUXu hWXu
    hdUW hdUX hdWX hXlo hXhi hWlo hWhi hUlo hUhi
  refine ⟨Bad, hBadcard, le_trans (prune_le _ _) (tripleGraph_le G U W X), ?_, ?_, ?_⟩
  · exact (prune_near_regular (tripleGraph G U W X) Bad ht
      (fun e he hnb => (hBad e he hnb).2) (fun e he hnb => (hBad e he hnb).1)).1
  · obtain ⟨Exc, hExc, hlo⟩ := (prune_near_regular_local (tripleGraph G U W X) Bad ht
      (D := #U + #W + #X) (tripleGraph_degree_le G U W X)
      (fun e he hnb => (hBad e he hnb).2) (fun e he hnb => (hBad e he hnb).1)).2
    refine ⟨Exc, ?_, hlo⟩
    refine le_trans hExc (le_of_eq ?_)
    push_cast
    ring
  · exact card_cliqueFinset_two_prune_ge (tripleGraph G U W X) Bad

end Nibble.AX1

end


/-! # CoreGapDesignLocal -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The support size `|A| + |B| + |C|` of a sub-triple: the localised replacement for `|V|` in the
exceptional-edge clause of a design. -/
@[expose]
noncomputable def designSupport (A B C : Finset V) : ℝ := (#A : ℝ) + (#B : ℝ) + (#C : ℝ)

/-- **A local sub-triple design.**  The shape of `Nibble.AX1.IsSubTripleShape` together with the
global clauses, the exceptional-edge clause now being charged against the *support* of the
sub-triple rather than against the whole vertex set. -/
@[expose]
def IsSubTripleDesignLocal (G : SimpleGraph V) [DecidableRel G.Adj] (ε μ η d₀ ε₂ μ₂ t : ℝ) (k : ℕ)
    (A B C : ℕ → Finset V) (d Elo : ℕ → ℝ) : Prop :=
  IsSubTripleShape G ε₂ μ₂ k A B C d ∧
  0 < ε₂ ∧ ε₂ ≤ 1 ∧ 0 < t ∧ 0 ≤ η ∧ μ₂ ≤ μ ∧
  (∀ i < k, d₀ ≤ d i) ∧ (∀ i < k, 0 ≤ d i) ∧
  (∀ i < k, 2 * t ≤ (μ - μ₂) * d i) ∧
  (∀ i < k, Elo i ≤ (#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℝ)) ∧
  (∀ i < k, (2 * designBad ε₂ (A i) (B i) (C i) / t) * designSupport (A i) (B i) (C i)
    ≤ η * (Elo i - designBad ε₂ (A i) (B i) (C i))) ∧
  nu3star G ≤ (∑ i ∈ Finset.range k,
    (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3) + ε * (Fintype.card V : ℝ) ^ 2

/-- **The bridge from a local sub-triple design to a near-regular family.**  Identical to
`Nibble.AX1.hasNearRegularFamily_of_subTripleDesign` except that the exceptional edges of each
member are charged against the support of that member, via
`Nibble.AX1.uniform_triple_member_local`. -/
theorem hasNearRegularFamily_of_subTripleDesignLocal (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ ε₂ μ₂ t : ℝ} {k : ℕ} {A B C : ℕ → Finset V} {d Elo : ℕ → ℝ}
    (h : IsSubTripleDesignLocal G ε μ η d₀ ε₂ μ₂ t k A B C d Elo) :
    HasNearRegularFamily G ε μ η d₀ := by
  classical
  obtain ⟨hshape, hε₂, hε₂1, ht, hη, hμ₂, hd₀, hdnn, hslack, hElo, hexc, hcover⟩ := h
  obtain ⟨hdAB, hdAC, hdBC, huAB, huAC, huBC, hρAB, hρAC, hρBC, hClo, hChi, hBlo, hBhi, hAlo,
    hAhi, hpair⟩ := hshape
  -- the member attached to the `i`-th sub-triple
  have hmem : ∀ i : ℕ, ∃ Bad : Finset (Finset V), i < k →
      (((#Bad : ℕ) : ℝ) ≤ designBad ε₂ (A i) (B i) (C i) ∧
        prune (tripleGraph G (A i) (B i) (C i)) Bad ≤ G ∧
        (∀ e ∈ (prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2,
          (edgeTriangleDegree (prune (tripleGraph G (A i) (B i) (C i)) Bad) e : ℝ)
            ≤ (1 + μ₂) * d i) ∧
        (∃ Exc : Finset (Finset V),
          ((#Exc : ℕ) : ℝ) ≤ (2 * ((#Bad : ℕ) : ℝ) / t) * designSupport (A i) (B i) (C i) ∧
          ∀ e ∈ (prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2, e ∉ Exc →
            (1 - μ₂) * d i - 2 * t
              ≤ (edgeTriangleDegree (prune (tripleGraph G (A i) (B i) (C i)) Bad) e : ℝ)) ∧
        ((#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2) : ℕ) : ℝ)) := by
    intro i
    by_cases hi : i < k
    · obtain ⟨Bad, h1, h2, h3, h4, h5⟩ :=
        uniform_triple_member_local G (hdAB i hi) (hdAC i hi) (hdBC i hi) hε₂ hε₂1 ht
          (huAB i hi) (huAC i hi) (huBC i hi) (hρAB i hi) (hρAC i hi) (hρBC i hi)
          (hClo i hi) (hChi i hi) (hBlo i hi) (hBhi i hi) (hAlo i hi) (hAhi i hi)
      exact ⟨Bad, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Bad hBad using hmem
  refine ⟨k, fun i => prune (tripleGraph G (A i) (B i) (C i)) (Bad i), d, ?_, ?_, hd₀, ?_, ?_, ?_⟩
  · exact fun i hi => (hBad i hi).2.1
  · intro i hi j hj hij x y hxi hxj
    exact hpair i hi j hj hij x y (prune_le _ _ hxi) (prune_le _ _ hxj)
  · intro i hi e he
    have h := (hBad i hi).2.2.1 e he
    have hle : (1 + μ₂) * d i ≤ (1 + μ) * d i := by
      have := hdnn i hi; nlinarith
    linarith
  · intro i hi
    obtain ⟨Exc, hExc, hlo⟩ := (hBad i hi).2.2.2.1
    refine ⟨Exc, ?_, ?_⟩
    · have hBadle : ((#(Bad i) : ℕ) : ℝ) ≤ designBad ε₂ (A i) (B i) (C i) := (hBad i hi).1
      have hsupp : 0 ≤ designSupport (A i) (B i) (C i) := by
        unfold designSupport; positivity
      have hmono : (2 * ((#(Bad i) : ℕ) : ℝ) / t) * designSupport (A i) (B i) (C i)
          ≤ (2 * designBad ε₂ (A i) (B i) (C i) / t) * designSupport (A i) (B i) (C i) := by
        have hd : 2 * ((#(Bad i) : ℕ) : ℝ) / t ≤ 2 * designBad ε₂ (A i) (B i) (C i) / t := by
          gcongr
        exact mul_le_mul_of_nonneg_right hd hsupp
      have hsurv : Elo i - designBad ε₂ (A i) (B i) (C i)
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2) : ℕ) : ℝ) := by
        have h5 := (hBad i hi).2.2.2.2
        have := hElo i hi
        linarith
      have hex := hexc i hi
      have hη' : η * (Elo i - designBad ε₂ (A i) (B i) (C i))
          ≤ η * ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsurv hη
      linarith
    · intro e he hne
      have h := hlo e he hne
      have := hslack i hi
      linarith
  · refine le_trans hcover ?_
    have hterm : ∀ i ∈ Finset.range k,
        (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2)
              : ℕ) : ℝ) / 3 := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h5 := (hBad i hi).2.2.2.2
      have h1 := (hBad i hi).1
      have := hElo i hi
      linarith
    have := Finset.sum_le_sum hterm
    linarith

end Nibble.AX1

end



/-! # CoreGapGridResidual -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **The design form of the reduced residual at parameters `(ε, μ, η, d₀)` and regularity scale
`ε₁`**: every triangle-rich regularity-reduced graph carries a sub-triple design in the sense of
`Nibble.AX1.IsSubTripleDesign`. -/
def SubTripleDesignAt (ε μ η d₀ ε₁ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)),
    n₀ ≤ Fintype.card V →
    P.IsEquipartition →
    4 / ε₁ ≤ (P.parts.card : ℝ) →
    (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
    P.IsUniform G (ε₁ / 8) →
    SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3
      ≤ ((((G.regularityReduced P (ε₁ / 8) (ε₁ / 4))).cliqueFinset 3).card : ℝ) →
    ∃ (ε₂ μ₂ t : ℝ) (k : ℕ) (A B C : ℕ → Finset V) (d Elo : ℕ → ℝ),
      IsSubTripleDesign (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀ ε₂ μ₂ t k A B C d Elo

/-- **The design residual**: a sub-triple design at every window of parameters, for some regularity
scale `ε₁` as small as one likes. -/
def SubTripleDesignResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ ≤ 1 ∧ SubTripleDesignAt ε μ η d₀ ε₁

/-- **A design gives the reduced family.** -/
theorem reducedFamilyAt_of_subTripleDesignAt {ε μ η d₀ ε₁ : ℝ}
    (h : SubTripleDesignAt ε μ η d₀ ε₁) : ReducedFamilyAt ε μ η d₀ ε₁ := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu hrich
  obtain ⟨ε₂, μ₂, t, k, A, B, C, d, Elo, hdes⟩ := hmain V G P hV hP hPl hPb hPu hrich
  exact hasNearRegularFamily_of_isSubTripleDesign _ hdes

/-- **The design residual implies the structural residual `Nibble.AX1.ReducedFamilyResidual`.** -/
theorem reducedFamilyResidual_of_subTripleDesign (h : SubTripleDesignResidual) :
    ReducedFamilyResidual := by
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨ε₁, hε₁, hε₁ε, hε₁1, hdes⟩ := h ε hε μ hμ η hη d₀ hd₀
  exact ⟨ε₁, hε₁, hε₁ε, hε₁1, reducedFamilyAt_of_subTripleDesignAt hdes⟩

/-- **AX1 from the design residual.** -/
theorem ax1_of_subTripleDesign (h : SubTripleDesignResidual) : AX1Statement :=
  ax1_of_reducedFamily (reducedFamilyResidual_of_subTripleDesign h)

end Nibble.AX1

end


/-! # CoreGapGridLocalResidual -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **The local design form of the reduced residual at parameters `(ε, μ, η, d₀)` and regularity
scale `ε₁`**: every triangle-rich regularity-reduced graph carries a sub-triple design in the sense
of `Nibble.AX1.IsSubTripleDesignLocal`. -/
@[expose]
def SubTripleDesignLocalAt (ε μ η d₀ ε₁ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)),
    n₀ ≤ Fintype.card V →
    P.IsEquipartition →
    4 / ε₁ ≤ (P.parts.card : ℝ) →
    (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
    P.IsUniform G (ε₁ / 8) →
    SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3
      ≤ ((((G.regularityReduced P (ε₁ / 8) (ε₁ / 4))).cliqueFinset 3).card : ℝ) →
    ∃ (ε₂ μ₂ t : ℝ) (k : ℕ) (A B C : ℕ → Finset V) (d Elo : ℕ → ℝ),
      IsSubTripleDesignLocal (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀ ε₂ μ₂ t k A B C
        d Elo

/-- **The local design residual**: a local sub-triple design at every window of parameters, for
some regularity scale `ε₁` as small as one likes. -/
@[expose]
def SubTripleDesignLocalResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ ≤ 1 ∧ SubTripleDesignLocalAt ε μ η d₀ ε₁

/-- **A local design gives the reduced family.** -/
theorem reducedFamilyAt_of_subTripleDesignLocalAt {ε μ η d₀ ε₁ : ℝ}
    (h : SubTripleDesignLocalAt ε μ η d₀ ε₁) : ReducedFamilyAt ε μ η d₀ ε₁ := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu hrich
  obtain ⟨ε₂, μ₂, t, k, A, B, C, d, Elo, hdes⟩ := hmain V G P hV hP hPl hPb hPu hrich
  exact hasNearRegularFamily_of_subTripleDesignLocal _ hdes

/-- **The local design residual implies the structural residual
`Nibble.AX1.ReducedFamilyResidual`.** -/
theorem reducedFamilyResidual_of_subTripleDesignLocal (h : SubTripleDesignLocalResidual) :
    ReducedFamilyResidual := by
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨ε₁, hε₁, hε₁ε, hε₁1, hdes⟩ := h ε hε μ hμ η hη d₀ hd₀
  exact ⟨ε₁, hε₁, hε₁ε, hε₁1, reducedFamilyAt_of_subTripleDesignLocalAt hdes⟩

/-- **AX1 from the local design residual.** -/
theorem ax1_of_subTripleDesignLocal (h : SubTripleDesignLocalResidual) : AX1Statement :=
  ax1_of_reducedFamily (reducedFamilyResidual_of_subTripleDesignLocal h)

end Nibble.AX1
