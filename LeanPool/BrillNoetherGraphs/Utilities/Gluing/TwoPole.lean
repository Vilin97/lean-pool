/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.EdgeAddition
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeGraph

/-!
# Two-pole joins

This file packages the graph obtained by joining two pointed graphs at two
ordered pairs of poles.  One cross-edge is installed as a separating bridge;
the second is then an `addEdge`.  This presentation exposes the unique seam
phase created by the second edge while keeping divisors on the two factors as
literal functions on a sum type.

The API is deliberately divisor-generic.  `sumDivisor` combines arbitrary
factor divisors, `phase` records the integral seam orbit, and the canonical
specialization identifies the residual of the local canonical sum with the
four pole chips.  In genus two plus genus two, Riemann--Roch therefore says
that the two degree-four candidates have exactly the same rank.
-/

open Finset

namespace Utilities

universe u v

/-- A graph equipped with two ordered poles.  The poles are allowed to
coincide; the two cross-edges of a join are nevertheless loopless because
they run between the two summands. -/
structure TwoPole (G : CFGraph.{u}) where
  first : G.V
  second : G.V

namespace TwoPole

/-- The lower-genus presentation of a two-pole join: retain only the first
cross-edge, which is a separating bridge. -/
abbrev bridge (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B) : CFGraph.{max u v} :=
  bridgeGraph A B p.first q.first

/-- Join two graphs by matching their first poles and their second poles. -/
abbrev join (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B) : CFGraph.{max u v} :=
  addEdge (bridge A B p q) (Sum.inl p.second) (Sum.inr q.second) (by
    change (Sum.inl p.second : Sum A.V B.V) ≠ Sum.inr q.second
    simp)

/-- The endpoints of the second cross-edge are distinct, independently of
whether either pair of poles coincides within its factor. -/
theorem second_endpoints_ne (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B) :
    (Sum.inl p.second : (bridge A B p q).V) ≠ Sum.inr q.second := by
  exact Sum.inl_ne_inr

/-- Add divisors on the two factors by placing them on the two summands.  The
same function is a divisor on both `bridge` and `join`, since `addEdge` keeps
the vertex type unchanged. -/
def sumDivisor (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B) (D : CFDiv A) (E : CFDiv B) :
    CFDiv (join A B p q) :=
  Sum.elim D E

@[simp] theorem sumDivisor_inl
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (a : A.V) :
    sumDivisor A B p q D E (Sum.inl a) = D a := rfl

@[simp] theorem sumDivisor_inr
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (b : B.V) :
    sumDivisor A B p q D E (Sum.inr b) = E b := rfl

/-! ## The seam phase orbit -/

/-- Translate a divisor through the integral seam orbit created by the second
cross-edge.  This is the phase coordinate that has to be chosen when the
one-bridge seed is lifted to a genuine two-pole join. -/
def phase (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv (join A B p q)) (n : ℤ) : CFDiv (join A B p q) :=
  D + n • seamDivisor (Sum.inl p.second) (Sum.inr q.second)

@[simp] theorem phase_zero
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv (join A B p q)) :
    phase A B p q D 0 = D := by
  simp [phase]

/-- Phases form an additive integral orbit. -/
theorem phase_add
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv (join A B p q)) (m n : ℤ) :
    phase A B p q (phase A B p q D m) n = phase A B p q D (m + n) := by
  unfold phase
  rw [add_smul]
  abel

@[simp] theorem deg_phase
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv (join A B p q)) (n : ℤ) :
    deg (phase A B p q D n) = deg D := by
  exact deg_add_zsmul_seamDivisor D _ _ n
/-- On a factor sum, changing phase credits the second left pole and debits
the second right pole. -/
theorem phase_sumDivisor
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (n : ℤ) :
    phase A B p q (sumDivisor A B p q D E) n =
      sumDivisor A B p q
        (D + n • oneChip p.second) (E - n • oneChip q.second) := by
  funext z
  cases z with
  | inl a =>
      by_cases ha : a = p.second
      · subst a
        simp [phase, seamDivisor, oneChip]
      · have hSum :
            (Sum.inl a : (join A B p q).V) ≠ Sum.inl p.second :=
          fun h => ha (Sum.inl.inj h)
        simp [phase, seamDivisor, oneChip, ha, hSum]
  | inr b =>
      by_cases hb : b = q.second
      · subst b
        simp [phase, seamDivisor, oneChip]
        ring
      · have hSum :
            (Sum.inr b : (join A B p q).V) ≠ Sum.inr q.second :=
          fun h => hb (Sum.inr.inj h)
        simp [phase, seamDivisor, oneChip, hb, hSum]
/-- Degrees add under the literal sum of factor divisors. -/
@[simp] theorem deg_sumDivisor
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) :
    deg (sumDivisor A B p q D E) = deg D + deg E := by
  change (∑ z : Sum A.V B.V, Sum.elim D E z) =
    (∑ a : A.V, D a) + ∑ b : B.V, E b
  rw [Fintype.sum_sum_type]
  simp

/-- Effectivity of a factor sum is exactly factorwise effectivity. -/
@[simp] theorem effective_sumDivisor_iff
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) :
    effective (sumDivisor A B p q D E) ↔ effective D ∧ effective E := by
  constructor
  · intro h
    exact ⟨fun a => h (Sum.inl a), fun b => h (Sum.inr b)⟩
  · rintro ⟨hD, hE⟩ z
    cases z with
    | inl a => exact hD a
    | inr b => exact hE b

/-- The degree of a left vertex in the one-bridge presentation. -/
theorem vertex_degree_bridge_inl
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (a : A.V) :
    vertexDegree (bridge A B p q) (Sum.inl a) =
      vertexDegree A a + if a = p.first then 1 else 0 := by
  unfold vertexDegree bridge
  change (∑ z : Sum A.V B.V,
    (numEdges (bridgeGraph A B p.first q.first) (Sum.inl a) z : ℤ)) = _
  rw [Fintype.sum_sum_type]
  simp_rw [num_edges_bridgeGraph_inl, num_edges_bridgeGraph_inl_inr]
  by_cases ha : a = p.first
  · subst a
    simp only [if_pos, true_and, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_ite_eq' Finset.univ q.first]
    simp
  · simp [ha]
/-- The degree of a right vertex in the one-bridge presentation. -/
theorem vertex_degree_bridge_inr
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (b : B.V) :
    vertexDegree (bridge A B p q) (Sum.inr b) =
      vertexDegree B b + if b = q.first then 1 else 0 := by
  unfold vertexDegree bridge
  change (∑ z : Sum A.V B.V,
    (numEdges (bridgeGraph A B p.first q.first) (Sum.inr b) z : ℤ)) = _
  rw [Fintype.sum_sum_type]
  simp_rw [num_edges_symmetric, num_edges_bridgeGraph_inl_inr,
    num_edges_bridgeGraph_inr]
  by_cases hb : b = q.first
  · subst b
    simp only [if_pos, and_true, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_ite_eq' Finset.univ p.first]
    simp only [Finset.mem_univ, ite_true]
    abel
  · simp [hb]
/-- The canonical divisor of the bridge presentation is the sum of the two
factor canonical divisors plus one chip at each bridge endpoint. -/
theorem canonical_divisor_bridge
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B) :
    canonicalDivisor (bridge A B p q) =
      fun z => Sum.elim (canonicalDivisor A) (canonicalDivisor B) z +
        oneChip (G := bridge A B p q) (Sum.inl p.first) z +
          oneChip (G := bridge A B p q) (Sum.inr q.first) z := by
  funext z
  unfold canonicalDivisor
  cases z with
  | inl a =>
      rw [vertex_degree_bridge_inl]
      by_cases ha : a = p.first
      · subst a
        simp [oneChip]
        ring
      · simp only [oneChip]
        rw [if_neg (fun h => ha (Sum.inl.inj h)), if_neg Sum.inl_ne_inr]
        simp only [Sum.elim_inl]
        rw [if_neg ha]
        ring
  | inr b =>
      rw [vertex_degree_bridge_inr]
      by_cases hb : b = q.first
      · subst b
        simp [oneChip]
        ring
      · simp only [oneChip]
        rw [if_neg Sum.inr_ne_inl, if_neg (fun h => hb (Sum.inr.inj h))]
        simp only [Sum.elim_inr]
        rw [if_neg hb]
        ring

/-- The four pole chips, regarded as a divisor on the two-pole join. -/
def boundaryDivisor (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B) : CFDiv (join A B p q) :=
  oneChip (Sum.inl p.first) + oneChip (Sum.inl p.second) +
    oneChip (Sum.inr q.first) + oneChip (Sum.inr q.second)

/-- The sum of the two local canonical divisors, with no pole chips added. -/
def canonicalSum (A : CFGraph.{u}) (B : CFGraph.{v})
    (p : TwoPole A) (q : TwoPole B) : CFDiv (join A B p q) :=
  sumDivisor A B p q (canonicalDivisor A) (canonicalDivisor B)
/-- Adding the second cross-edge creates one cycle. -/
@[simp] theorem genus_join
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B) :
    genus (join A B p q) = genus A + genus B + 1 := by
  rw [join, genus_addEdge, bridge, genus_bridgeGraph]

/-- A two-pole join of connected factors is connected. -/
theorem connected_join
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (hA : graphConnected A) (hB : graphConnected B) :
    graphConnected (join A B p q) := by
  apply graph_connected_addEdge
  exact graph_connected_bridgeGraph A B p.first q.first hA hB
@[simp] theorem deg_boundaryDivisor
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B) :
    deg (boundaryDivisor A B p q) = 4 := by
  simp only [boundaryDivisor, deg.map_add, deg_one_chip]
  norm_num

@[simp] theorem deg_canonicalSum
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B) :
    deg (canonicalSum A B p q) = 2 * genus A + 2 * genus B - 4 := by
  change deg (sumDivisor A B p q (canonicalDivisor A) (canonicalDivisor B)) = _
  rw [deg_sumDivisor]
  simp only [degree_of_canonical_divisor]
  ring
/-- Canonical bookkeeping for a two-pole join.  The global canonical divisor
is the local canonical sum plus exactly the four pole chips. -/
theorem canonical_divisor_join
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B) :
    canonicalDivisor (join A B p q) =
      canonicalSum A B p q + boundaryDivisor A B p q := by
  unfold join
  rw [canonical_divisor_addEdge]
  funext z
  have hBridge := congrFun (canonical_divisor_bridge A B p q) z
  cases z with
  | inl a =>
      simp only [Pi.add_apply, canonicalSum, sumDivisor_inl, boundaryDivisor]
      rw [hBridge]
      simp only [Sum.elim_inl]
      simp [oneChip]
      ring
  | inr b =>
      simp only [Pi.add_apply, canonicalSum, sumDivisor_inr, boundaryDivisor]
      rw [hBridge]
      simp only [Sum.elim_inr]
      simp [oneChip]
      ring

/-- The four pole chips are literally the canonical complement of the local
canonical sum. -/
theorem canonical_sub_canonicalSum
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B) :
    canonicalDivisor (join A B p q) - canonicalSum A B p q =
      boundaryDivisor A B p q := by
  rw [canonical_divisor_join]
  abel

/-- General Riemann--Roch comparison between the two canonical halves of a
two-pole join. -/
theorem rank_canonicalSum_sub_rank_boundary
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (hA : graphConnected A) (hB : graphConnected B) :
    rank (join A B p q) (canonicalSum A B p q) -
        rank (join A B p q) (boundaryDivisor A B p q) =
      genus A + genus B - 4 := by
  have hRR := riemann_roch_for_graphs
    (connected_join A B p q hA hB) (canonicalSum A B p q)
  rw [canonical_sub_canonicalSum, deg_canonicalSum, genus_join] at hRR
  linarith

/-- **The genus-two `K_A+K_B` duality lemma.**  On a two-pole join of two
connected genus-two graphs, the local canonical sum and the four pole chips
have equal rank.  Thus either one may be used as the unmarked degree-four
witness. -/
theorem rank_canonicalSum_eq_rank_boundary_of_genus_two
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (hA : graphConnected A) (hGenusA : genus A = 2)
    (hB : graphConnected B) (hGenusB : genus B = 2) :
    rank (join A B p q) (canonicalSum A B p q) =
      rank (join A B p q) (boundaryDivisor A B p q) := by
  have h := rank_canonicalSum_sub_rank_boundary A B p q hA hB
  rw [hGenusA, hGenusB] at h
  omega

end TwoPole

end Utilities
