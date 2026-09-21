/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gonality.LegalFiring
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.OrientationReversal
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne

/-!
# Orientation divisors and rank one

`ordiv G O = indeg_O - 1` has degree `g - 1`, so the orientation model is a
natural setting for the critical pencil `(1, g-1)`.

`legal_of_ordiv_iff` characterizes the legal firing sets of an orientation
divisor. The main sufficient criterion,
`rank_ge_one_of_inHeavyReachable`, says that `ordiv G O` has rank at least one
when its class contains, for each vertex `q`, a source-free orientation with
`2 ≤ indeg q`. By `gioan_reversalEquiv_of_linear_equiv`, this hypothesis can
also be expressed as reachability in the cycle--cocycle reversal system.
-/

namespace Utilities.Gonality

open Finset Utilities

variable {G : CFGraph}

/-! ## Source-free orientations: the floor -/

/-- `O` has no source: every vertex receives at least one edge. -/
def SourceFree (O : CFOrientation G) : Prop := ∀ v : G.V, 1 ≤ indeg G O v

/-- `O` is *in-heavy at `q`*: source-free, and `q` receives at least two edges. This is
exactly the condition making `ordiv G O - one_chip q` effective. -/
def InHeavyAt (O : CFOrientation G) (q : G.V) : Prop :=
  SourceFree O ∧ 2 ≤ indeg G O q

theorem InHeavyAt.sourceFree {O : CFOrientation G} {q : G.V} (h : InHeavyAt O q) :
    SourceFree O := h.1

/-- A source-free orientation has an effective divisor. -/
theorem effective_ordiv_of_sourceFree {O : CFOrientation G} (h : SourceFree O) :
    effective (ordiv G O) := by
  intro v
  have := h v
  simp only [ordiv]
  omega

/-- `rank (ordiv G O) ≥ 0` for a source-free orientation. -/
theorem winnable_ordiv_of_sourceFree {O : CFOrientation G} (h : SourceFree O) :
    winnable G (ordiv G O) :=
  ⟨ordiv G O, effective_ordiv_of_sourceFree h, linear_equiv.refl G _⟩

/-- In-heaviness at `q` is exactly effectivity of `ordiv G O - one_chip q`. -/
theorem effective_ordiv_sub_one_chip_of_inHeavyAt {O : CFOrientation G} {q : G.V}
    (h : InHeavyAt O q) : effective (ordiv G O - one_chip q) := by
  intro v
  by_cases hv : v = q
  · subst hv
    have := h.2
    simp only [Pi.sub_apply, ordiv, one_chip]
    omega
  · have := h.1 v
    simp only [Pi.sub_apply, ordiv, one_chip, if_neg hv]
    omega

/-! ## The surviving statement: in-heavy reachability certifies rank one -/

/-- Subtracting the same chip from both sides of a linear equivalence. -/
private theorem linear_equiv_sub_one_chip {D D' : CFDiv G} (h : linear_equiv G D D')
    (q : G.V) : linear_equiv G (D - one_chip q) (D' - one_chip q) := by
  simpa only [linear_equiv, sub_sub_sub_cancel_right] using h

/-- **In-heavy reachability certifies rank one.**  If the divisor class of `ordiv G O`
contains, for every vertex `q`, an orientation divisor that is source-free and in-heavy at
`q`, then `rank G (ordiv G O) ≥ 1`.

By `gioan_reversalEquiv_of_linear_equiv` the hypothesis is equivalent to reachability of
such an orientation from `O` in the cycle–cocycle reversal system, which is the form the
distillation note states.  The converse fails — see the module docstring. -/
theorem rank_ge_one_of_inHeavyReachable (O : CFOrientation G)
    (h : ∀ q : G.V, ∃ O' : CFOrientation G,
      linear_equiv G (ordiv G O) (ordiv G O') ∧ InHeavyAt O' q) :
    rank G (ordiv G O) ≥ 1 := by
  refine rank_ge_one_of_vertex_certificates G (ordiv G O) fun q => ?_
  obtain ⟨O', hequiv, hheavy⟩ := h q
  exact ⟨ordiv G O' - one_chip q, effective_ordiv_sub_one_chip_of_inHeavyAt hheavy,
    linear_equiv_sub_one_chip hequiv q⟩

/-- The same statement with the reachability hypothesis phrased through the reversal
system, using Gioan's theorem in the direction already proved in
`Utilities/Foundations/OrientationReversal.lean`. -/
theorem rank_ge_one_of_inHeavyReachable' (O : CFOrientation G)
    (h : ∀ q : G.V, ∃ O' : CFOrientation G,
      linear_equiv G (ordiv G O) (ordiv G O') ∧ SourceFree O' ∧ 2 ≤ indeg G O' q) :
    rank G (ordiv G O) ≥ 1 :=
  rank_ge_one_of_inHeavyReachable O fun q =>
    let ⟨O', he, hs, hq⟩ := h q; ⟨O', he, ⟨hs, hq⟩⟩

/-! ## Why strong connectivity is an obstruction

Dhar's fire on `ordiv G O` reads only the induced subdigraph on the unburnt set. -/

/-- The arcs of `O` with both ends in `U`, counted at their heads. -/
def arcsWithin (O : CFOrientation G) (U : Finset G.V) : ℕ :=
  ∑ u ∈ U, ∑ w ∈ U, flow O w u

/-- The arcs of `O` leaving `U`. -/
def arcsOut (O : CFOrientation G) (U : Finset G.V) : ℕ :=
  ∑ u ∈ U, ∑ w ∈ Uᶜ, flow O u w

/-- **Legality for an orientation divisor is intrinsic to the induced subdigraph.**

`u ∈ U` can pay its whole boundary out of `ordiv G O` exactly when it receives strictly
more arcs from inside `U` than it sends outside `U`.  The arcs entering `u` *from outside*
`U` cancel: they are counted once by `indeg` and once by `outdeg_S`.

The characterization is expressed entirely in terms of arc counts inside and
across the boundary of `U`. -/
theorem legal_of_ordiv_iff (O : CFOrientation G) (U : Finset G.V) (u : G.V) :
    outdeg_S G U u ≤ ordiv G O u ↔
      (∑ w ∈ Uᶜ, flow O u w) + 1 ≤ ∑ w ∈ U, flow O w u := by
  classical
  have hout : outdeg_S G U u
      = (∑ w ∈ Uᶜ, (flow O u w : ℤ)) + ∑ w ∈ Uᶜ, (flow O w u : ℤ) := by
    rw [outdeg_S, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← flow_add_flow_rev O u w]
    push_cast
    ring
  have hin : (ordiv G O) u
      = ((∑ w ∈ U, (flow O w u : ℤ)) + ∑ w ∈ Uᶜ, (flow O w u : ℤ)) - 1 := by
    have h := indeg_eq_sum_flow O u
    simp only [ordiv]
    rw [h]
    push_cast
    rw [Finset.sum_add_sum_compl U (fun w => (flow O w u : ℤ))]
  rw [hout, hin]
  constructor
  · intro hle
    have : (∑ w ∈ Uᶜ, (flow O u w : ℤ)) + 1 ≤ ∑ w ∈ U, (flow O w u : ℤ) := by linarith
    exact_mod_cast this
  · intro hle
    have : (∑ w ∈ Uᶜ, (flow O u w : ℤ)) + 1 ≤ ∑ w ∈ U, (flow O w u : ℤ) := by
      exact_mod_cast hle
    linarith

/-- **The counting corollary.**  A set that Dhar's fire fails to burn must induce a
subdigraph with at least `|U| + (arcs leaving U)` internal arcs.

For a strongly connected `O` every proper nonempty `U` has `1 ≤ arcsOut O U`, so every
legal set induces a subgraph with strictly more edges than vertices — first Betti number at
least two once the boundary is counted.  On sparse graphs (cubic cores, say) such sets are
rare, `ordiv G O` is already `q`-reduced at the in-degree-one vertices, and the rank is
zero.  That is the whole failure. -/
theorem card_add_arcsOut_le_arcsWithin_of_legal (O : CFOrientation G) (U : Finset G.V)
    (h : ∀ u ∈ U, outdeg_S G U u ≤ ordiv G O u) :
    U.card + arcsOut O U ≤ arcsWithin O U := by
  classical
  have hpt : ∀ u ∈ U, 1 + ∑ w ∈ Uᶜ, flow O u w ≤ ∑ w ∈ U, flow O w u := by
    intro u hu
    have := (legal_of_ordiv_iff O U u).mp (h u hu)
    omega
  calc U.card + arcsOut O U
      = ∑ u ∈ U, (1 + ∑ w ∈ Uᶜ, flow O u w) := by
        rw [Finset.sum_add_distrib, arcsOut, Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ u ∈ U, ∑ w ∈ U, flow O w u := Finset.sum_le_sum hpt
    _ = arcsWithin O U := rfl

/-- The contrapositive, in the form the failure analysis uses: a set too sparse inside, or
leaking too many arcs, cannot be unburnt. -/
theorem not_legal_of_arcsWithin_lt (O : CFOrientation G) (U : Finset G.V)
    (h : arcsWithin O U < U.card + arcsOut O U) :
    ¬ (∀ u ∈ U, outdeg_S G U u ≤ ordiv G O u) := fun hlegal =>
  absurd (card_add_arcsOut_le_arcsWithin_of_legal O U hlegal) (by omega)

end Utilities.Gonality
