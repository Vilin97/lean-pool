/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegree

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the LINEAR sandwich for the safe degree

The safe degree `safeDegree H C v` (`LeanPool.AsymptoticTrianglePacking.Internal.SafeDegree`) is a
nonlinear functional of the covered
set `C` — it counts the edges at `v` *none* of whose other vertices is covered. Its concentration is
obtained here by sandwiching it between two quantities that are LINEAR (resp. quadratic) in the
covering indicators, which are the objects whose moments the exact one-round covering law
(`LeanPool.AsymptoticTrianglePacking.Internal.prob_vertex_covered_eq`,
`LeanPool.AsymptoticTrianglePacking.Internal.prob_two_vertices_covered_le`) controls:

* `coverWeight H v C = ∑_{u ∈ C, u ≠ v} codeg(v,u) = ∑_{e ∋ v} |(e∖v) ∩ C|` — the *loss weight*;
* `pairWeight H v C = ∑_{e ∋ v} C(|(e∖v) ∩ C|, 2)` — the Bonferroni correction.

The sandwich reads

  `deg(v) ≤ safeDeg(v) + coverWeight`   (`degree_le_safeDegree_add_coverWeight`),
  `safeDeg(v) + coverWeight ≤ deg(v) + pairWeight`   (`safeDegree_add_coverWeight_le`),

i.e. the loss `deg(v) − safeDeg(v)` is squeezed between `coverWeight − pairWeight` and
`coverWeight`.
Since `coverWeight` is a nonnegative combination `∑_u codeg(v,u)·1[u covered]` of the covering
indicators, its mean and variance are directly computable, and `pairWeight` has a small mean; this
is
what makes the SAFE degree concentrate where the residual degree cannot.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

/-- The loss weight of `v` against a covered set `C`: `∑_{u ∈ C, u ≠ v} codeg(v,u)`. -/
def coverWeight (H : Finset (Finset V)) (v : V) (C : Finset V) : ℕ :=
  ∑ u ∈ C.erase v, codegree H v u

/-- The Bonferroni correction: `∑_{e ∋ v} C(|(e∖v) ∩ C|, 2)`. -/
def pairWeight (H : Finset (Finset V)) (v : V) (C : Finset V) : ℕ :=
  ∑ e ∈ H.filter (fun e => v ∈ e), Nat.choose ((e.erase v ∩ C).card) 2

/-- `coverWeight` counted edge-by-edge: `∑_{e ∋ v} |(e∖v) ∩ C|`. -/
theorem coverWeight_eq_sum (H : Finset (Finset V)) (v : V) (C : Finset V) :
    coverWeight H v C = ∑ e ∈ H.filter (fun e => v ∈ e), (e.erase v ∩ C).card := by
  classical
  have h1 : ∀ u ∈ C.erase v,
      codegree H v u = ((H.filter (fun e => v ∈ e)).filter (fun e => u ∈ e)).card := by
    intro u _
    rw [codegree, Finset.filter_filter]
  have h2 : ∀ e ∈ H.filter (fun e => v ∈ e),
      (e.erase v ∩ C).card = ((C.erase v).filter (fun u => u ∈ e)).card := by
    intro e _
    congr 1
    ext u
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_filter]
    tauto
  rw [coverWeight, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The edges at `v` are split by safety. -/
theorem degree_eq_safeDegree_add (H : Finset (Finset V)) (v : V) (C : Finset V) :
    degree H v = safeDegree H C v
      + ((H.filter (fun e => v ∈ e)).filter (fun e => ¬ Disjoint (e.erase v) C)).card := by
  classical
  have hsafe : safeDegree H C v
      = ((H.filter (fun e => v ∈ e)).filter (fun e => Disjoint (e.erase v) C)).card := by
    rw [safeDegree, Finset.filter_filter]
  rw [hsafe, degree]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- An edge at `v` is unsafe exactly when it meets `C` outside `v`. -/
theorem unsafe_iff_inter_nonempty {e : Finset V} {v : V} {C : Finset V} :
    ¬ Disjoint (e.erase v) C ↔ 0 < (e.erase v ∩ C).card := by
  rw [Finset.card_pos, Finset.not_disjoint_iff_nonempty_inter]

/-- **Sandwich, lower half.**  `deg(v) ≤ safeDeg(v) + coverWeight`. -/
theorem degree_le_safeDegree_add_coverWeight (H : Finset (Finset V)) (v : V) (C : Finset V) :
    degree H v ≤ safeDegree H C v + coverWeight H v C := by
  classical
  rw [degree_eq_safeDegree_add H v C, coverWeight_eq_sum]
  refine Nat.add_le_add_left ?_ _
  calc ((H.filter (fun e => v ∈ e)).filter (fun e => ¬ Disjoint (e.erase v) C)).card
      = ∑ e ∈ H.filter (fun e => v ∈ e), if ¬ Disjoint (e.erase v) C then 1 else 0 :=
        Finset.card_filter _ _
    _ ≤ ∑ e ∈ H.filter (fun e => v ∈ e), (e.erase v ∩ C).card := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        by_cases h : Disjoint (e.erase v) C
        · simp [h]
        · simpa [h] using (unsafe_iff_inter_nonempty (e := e) (v := v) (C := C)).mp h

/-- The elementary Bonferroni step: `m ≤ 1[m ≥ 1] + C(m,2)`. -/
theorem nat_le_indicator_add_choose_two (m : ℕ) :
    m ≤ (if 0 < m then 1 else 0) + Nat.choose m 2 := by
  match m with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
      have hp : Nat.choose (k + 2) 2 = Nat.choose (k + 1) 1 + Nat.choose (k + 1) 2 :=
        Nat.choose_succ_succ (k + 1) 1
      rw [Nat.choose_one_right] at hp
      simp only [ite_eq_left (Nat.succ_pos (k + 1))]
      omega

/-- **Sandwich, upper half.**  `safeDeg(v) + coverWeight ≤ deg(v) + pairWeight`. -/
theorem safeDegree_add_coverWeight_le (H : Finset (Finset V)) (v : V) (C : Finset V) :
    safeDegree H C v + coverWeight H v C ≤ degree H v + pairWeight H v C := by
  classical
  rw [degree_eq_safeDegree_add H v C, coverWeight_eq_sum, pairWeight]
  rw [add_assoc]
  refine Nat.add_le_add_left ?_ _
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun e _ => ?_)
  have hb := nat_le_indicator_add_choose_two ((e.erase v ∩ C).card)
  have heq : (if ¬ Disjoint (e.erase v) C then (1 : ℕ) else 0)
      = (if 0 < (e.erase v ∩ C).card then 1 else 0) := by
    by_cases h : 0 < (e.erase v ∩ C).card
    · rw [ite_eq_left (unsafe_iff_inter_nonempty.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun hc => h (unsafe_iff_inter_nonempty.mp hc)), ite_eq_right h]
  rw [heq]
  exact hb

end LeanPool.AsymptoticTrianglePacking.Internal
