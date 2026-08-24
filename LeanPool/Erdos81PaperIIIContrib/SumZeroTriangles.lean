/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The sum-zero triple system: a near-perfect triangle packing of a complete graph

This file gives an explicit, constructive family of pairwise edge-disjoint triangles inside an
arbitrary finite vertex set `U` which leaves at most `3` uncovered edges at each vertex.

The construction is a *sum-zero* triple system. Label the `n = |U|` vertices
bijectively by the elements of the cyclic group `ZMod n` and take as triangles all triples of
distinct vertices whose labels sum to `0`.  Two such triples sharing an edge share two labels, and
the third label is then determined, so the triples are pairwise edge-disjoint.  A pair of distinct
labels `x ≠ y` fails to be covered only when the determined third label `-(x + y)` equals `x` or
`y`, that is, only when `y = -2x` or `2y = -x`; for fixed `x` there is at most one label `y` with
`y = -2x`, and at most two labels `y` with `2y = -x`, because the doubling map of `ZMod n` has
fibres of size at most `2`.  Hence at most `3` edges at each vertex remain uncovered.

## Main definitions

* `Finset.innerEdges`: the non-loop edges of the complete graph lying inside a finite set.
* `Finset.familyEdges`: the edges covered by a family of finite sets.
* `Finset.edgeDegree`: the number of edges of a given edge set incident to a vertex.
* `SumZeroTriangles.sumZeroTriples`: the triples of a labelled vertex set whose labels sum to zero.

## Main results

* `ZMod.card_filter_two_mul_eq_le`: every fibre of the doubling map `x ↦ 2 * x` of `ZMod n` has at
  most two elements.
* `SumZeroTriangles.sumZeroTriples_disjoint`: sum-zero triples with an injective labelling are
  pairwise edge-disjoint.
* `SumZeroTriangles.sumZeroTriples_edgeDegree_sdiff_le`: the sum-zero triple system leaves at most
  three uncovered edges at every vertex.
* `SumZeroTriangles.exists_triangle_packing_clique`: every finite vertex set carries a family of
  pairwise edge-disjoint triangles leaving at most three uncovered edges at every vertex.

## Implementation notes

Edges are modelled as elements of `Sym2 V`, and edge sets as `Finset (Sym2 V)`; a triangle is a
`Finset V` of cardinality `3` and the triangles of a family are required to have pairwise disjoint
edge sets.

-/

open Finset

namespace ZMod

/-- The kernel of the doubling map of `ZMod n` has at most two elements. -/
theorem card_filter_two_mul_eq_zero_le (n : ℕ) [NeZero n] :
    #{z : ZMod n | 2 * z = 0} ≤ 2 := by
  classical
  have hsub : (Finset.univ.filter fun z : ZMod n => 2 * z = 0)
      ⊆ ({0, ((n / 2 : ℕ) : ZMod n)} : Finset (ZMod n)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hval : z.val < n := ZMod.val_lt z
    have h2 : ((2 * z.val : ℕ) : ZMod n) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hz
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ n).1 h2
    have hk2 : k < 2 := by
      by_contra hcon
      push Not at hcon
      have : n * 2 ≤ n * k := Nat.mul_le_mul_left _ hcon
      omega
    have hcase : 2 * z.val = 0 ∨ 2 * z.val = n := by
      interval_cases k <;> omega
    have hz' := ZMod.natCast_zmod_val z
    rcases hcase with h | h
    · have hv : z.val = 0 := by omega
      rw [← hz', hv]
      simp
    · have hv : z.val = n / 2 := by omega
      rw [← hz', hv]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- Every fibre of the doubling map `x ↦ 2 * x` of `ZMod n` has at most two elements. -/
theorem card_filter_two_mul_eq_le (n : ℕ) [NeZero n] (c : ZMod n) :
    #{z : ZMod n | 2 * z = c} ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty {z : ZMod n | 2 * z = c} with h | ⟨z₀, hz₀⟩
  · simp [h]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz₀
    refine le_trans (Finset.card_le_card_of_injOn (fun z => z - z₀) ?_ ?_)
      (card_filter_two_mul_eq_zero_le n)
    · intro z hz
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hz ⊢
      rw [mul_sub, hz, hz₀, sub_self]
    · intro a _ b _ hab
      simpa using hab

end ZMod

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- The edges of the complete graph on `V` lying inside the finite set `s`, that is, the non-loop
unordered pairs both of whose entries belong to `s`. -/
def innerEdges (s : Finset V) : Finset (Sym2 V) :=
  s.sym2.filter fun e => ¬ e.IsDiag

@[simp]
lemma mem_innerEdges {s : Finset V} {e : Sym2 V} :
    e ∈ s.innerEdges ↔ (∀ v ∈ e, v ∈ s) ∧ ¬ e.IsDiag := by
  simp [innerEdges, Finset.mem_sym2_iff]

/-- The set of edges covered by a family `P` of finite vertex sets. -/
def familyEdges (P : Finset (Finset V)) : Finset (Sym2 V) :=
  P.biUnion innerEdges

lemma mem_familyEdges {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ familyEdges P ↔ ∃ t ∈ P, e ∈ t.innerEdges := by
  simp [familyEdges]

/-- The number of edges of the edge set `E` that are incident to the vertex `v`. -/
def edgeDegree (E : Finset (Sym2 V)) (v : V) : ℕ :=
  #{e ∈ E | v ∈ e}

end Finset

namespace SumZeroTriangles

variable {V : Type*} [DecidableEq V]

/-! ### The sum-zero triple system -/

/-- The triples of the vertex set `U`, labelled by `psi : V → ZMod n`, whose labels sum to zero. -/
def sumZeroTriples (n : ℕ) (U : Finset V) (psi : V → ZMod n) : Finset (Finset V) :=
  U.powerset.filter fun t => #t = 3 ∧ ∑ v ∈ t, psi v = 0

variable {n : ℕ} {U : Finset V} {psi : V → ZMod n}

omit [DecidableEq V] in
/-- Membership in `sumZeroTriples`: a triple of `U` with vanishing label sum. -/
lemma mem_sumZeroTriples {t : Finset V} :
    t ∈ sumZeroTriples n U psi ↔ t ⊆ U ∧ #t = 3 ∧ ∑ v ∈ t, psi v = 0 := by
  simp [sumZeroTriples, Finset.mem_powerset]

/-- In a three-element set containing the distinct elements `a` and `b` there is a unique third
element. -/
lemma exists_sdiff_pair_eq_singleton {t : Finset V} (ht : #t = 3) {a b : V} (ha : a ∈ t)
    (hb : b ∈ t) (hab : a ≠ b) : ∃ c, t \ ({a, b} : Finset V) = {c} := by
  have hsub : ({a, b} : Finset V) ⊆ t := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hb
  have hcard : #(t \ ({a, b} : Finset V)) = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, ht, Finset.card_pair hab]
  exact Finset.card_eq_one.1 hcard

/-- The label of the third vertex of a sum-zero triple is determined by the other two. -/
lemma third_label {t : Finset V} (ht : t ∈ sumZeroTriples n U psi) {a b c : V}
    (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b) (hc : t \ ({a, b} : Finset V) = {c}) :
    psi c = -(psi a + psi b) := by
  obtain ⟨-, -, hsum⟩ := mem_sumZeroTriples.1 ht
  have hsub : ({a, b} : Finset V) ⊆ t := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hb
  have hsplit := Finset.sum_sdiff (f := psi) hsub
  rw [hc, Finset.sum_singleton, Finset.sum_pair hab, hsum] at hsplit
  linear_combination hsplit

/-- The sum-zero triples of an injectively labelled vertex set are pairwise edge-disjoint. -/
lemma sumZeroTriples_disjoint (hinj : ∀ x ∈ U, ∀ y ∈ U, psi x = psi y → x = y) :
    ∀ t ∈ sumZeroTriples n U psi, ∀ t' ∈ sumZeroTriples n U psi, t ≠ t' →
      Disjoint t.innerEdges t'.innerEdges := by
  intro t ht t' ht' hne
  rw [Finset.disjoint_left]
  intro e het het'
  apply hne
  induction e with
  | h a b =>
    rw [Finset.mem_innerEdges] at het het'
    have hab : a ≠ b := by
      intro h
      exact het.2 (by simp [h])
    have ha : a ∈ t := het.1 a (by simp)
    have hb : b ∈ t := het.1 b (by simp)
    have ha' : a ∈ t' := het'.1 a (by simp)
    have hb' : b ∈ t' := het'.1 b (by simp)
    obtain ⟨htU, htc, -⟩ := mem_sumZeroTriples.1 ht
    obtain ⟨ht'U, ht'c, -⟩ := mem_sumZeroTriples.1 ht'
    obtain ⟨c, hc⟩ := exists_sdiff_pair_eq_singleton htc ha hb hab
    obtain ⟨c', hc'⟩ := exists_sdiff_pair_eq_singleton ht'c ha' hb' hab
    have hlab : psi c = psi c' := by
      rw [third_label ht ha hb hab hc, third_label ht' ha' hb' hab hc']
    have hcU : c ∈ U := htU (by
      have : c ∈ t \ ({a, b} : Finset V) := by rw [hc]; exact Finset.mem_singleton_self c
      exact (Finset.mem_sdiff.1 this).1)
    have hc'U : c' ∈ U := ht'U (by
      have : c' ∈ t' \ ({a, b} : Finset V) := by rw [hc']; exact Finset.mem_singleton_self c'
      exact (Finset.mem_sdiff.1 this).1)
    have hcc : c = c' := hinj c hcU c' hc'U hlab
    have hsub : ({a, b} : Finset V) ⊆ t := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton] at hx; exact hx ▸ hb
    have hsub' : ({a, b} : Finset V) ⊆ t' := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha'
      · rw [Finset.mem_singleton] at hx; exact hx ▸ hb'
    calc t = t \ ({a, b} : Finset V) ∪ ({a, b} : Finset V) :=
            (Finset.sdiff_union_of_subset hsub).symm
      _ = t' \ ({a, b} : Finset V) ∪ ({a, b} : Finset V) := by rw [hc, hc', hcc]
      _ = t' := Finset.sdiff_union_of_subset hsub'

/-- The canonical sum-zero triple through an edge whose two labels are not exceptional: it is a
genuine triple of `U` and its third vertex is distinct from the two endpoints. -/
lemma canonical_triple_mem (rho : ZMod n → V) (hrhoU : ∀ z, rho z ∈ U)
    (hrho : ∀ z, psi (rho z) = z) {a b : V} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (h1 : psi b ≠ -(2 * psi a)) (h2 : 2 * psi b ≠ -psi a) :
    ({a, b, rho (-(psi a + psi b))} : Finset V) ∈ sumZeroTriples n U psi ∧
      rho (-(psi a + psi b)) ≠ a ∧ rho (-(psi a + psi b)) ≠ b := by
  classical
  set c : V := rho (-(psi a + psi b))
  have hcU : c ∈ U := hrhoU _
  have hcl : psi c = -(psi a + psi b) := hrho _
  have hca : c ≠ a := by
    intro h
    apply h1
    have hpa : psi a = -(psi a + psi b) := by rw [← hcl, h]
    linear_combination hpa
  have hcb : c ≠ b := by
    intro h
    apply h2
    have hpb : psi b = -(psi a + psi b) := by rw [← hcl, h]
    linear_combination hpb
  refine ⟨?_, hca, hcb⟩
  set t : Finset V := {a, b, c} with htdef
  have htcard : #t = 3 := by
    rw [htdef, Finset.card_insert_of_notMem (by simp [hab, Ne.symm hca]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hcb]), Finset.card_singleton]
  have htsum : ∑ v ∈ t, psi v = 0 := by
    rw [htdef, Finset.sum_insert (by simp [hab, Ne.symm hca]),
      Finset.sum_insert (by simp [Ne.symm hcb]), Finset.sum_singleton, hcl]
    ring
  refine mem_sumZeroTriples.2 ⟨?_, htcard, htsum⟩
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact ha
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact hb
  · rw [Finset.mem_singleton] at hx; exact hx ▸ hcU

/-- The edge `s(a, b)` belongs to the edge set of the triple `{a, b, c}`. -/
lemma mem_innerEdges_triple {a b c : V} (hab : a ≠ b) :
    s(a, b) ∈ ({a, b, c} : Finset V).innerEdges := by
  rw [Finset.mem_innerEdges]
  refine ⟨?_, by simpa [Sym2.mk_isDiag_iff] using hab⟩
  intro v hv
  rcases Sym2.mem_iff.1 hv with rfl | rfl
  · simp
  · simp

/-- Every edge whose two labels are not in the exceptional relation is covered by the sum-zero
triple system. -/
lemma mem_familyEdges_sumZeroTriples (rho : ZMod n → V) (hrhoU : ∀ z, rho z ∈ U)
    (hrho : ∀ z, psi (rho z) = z) {a b : V} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (h1 : psi b ≠ -(2 * psi a)) (h2 : 2 * psi b ≠ -psi a) :
    s(a, b) ∈ familyEdges (sumZeroTriples n U psi) := by
  obtain ⟨htmem, -, -⟩ := canonical_triple_mem rho hrhoU hrho ha hb hab h1 h2
  exact Finset.mem_biUnion.2 ⟨_, htmem, mem_innerEdges_triple hab⟩

omit [DecidableEq V] in
/-- There are at most three exceptional partners of a vertex, that is, vertices `u ∈ U` whose label
satisfies `psi u = -2 * psi v` or `2 * psi u = -psi v`. -/
lemma card_exceptional_le [NeZero n] (hinj : ∀ x ∈ U, ∀ y ∈ U, psi x = psi y → x = y) (v : V) :
    #{u ∈ U | psi u = -(2 * psi v) ∨ 2 * psi u = -psi v} ≤ 3 := by
  classical
  have hsub : {u ∈ U | psi u = -(2 * psi v) ∨ 2 * psi u = -psi v}
      ⊆ {u ∈ U | psi u = -(2 * psi v)} ∪ {u ∈ U | 2 * psi u = -psi v} := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hu.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hu.1, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hu.1, h⟩)
  have hA : #{u ∈ U | psi u = -(2 * psi v)} ≤ 1 := by
    refine Finset.card_le_one.2 ?_
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    exact hinj x hx.1 y hy.1 (by rw [hx.2, hy.2])
  have hB : #{u ∈ U | 2 * psi u = -psi v} ≤ 2 := by
    refine le_trans (Finset.card_le_card_of_injOn psi ?_ ?_)
      (ZMod.card_filter_two_mul_eq_le n (-psi v))
    · intro u hu
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hu ⊢
      exact hu.2
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
      exact hinj x hx.1 y hy.1 hxy
  calc #{u ∈ U | psi u = -(2 * psi v) ∨ 2 * psi u = -psi v} ≤ _ := Finset.card_le_card hsub
    _ ≤ #{u ∈ U | psi u = -(2 * psi v)} + #{u ∈ U | 2 * psi u = -psi v} := Finset.card_union_le _ _
    _ ≤ 3 := by omega

/-- The uncovered degree of the sum-zero triple system is at most `3` at every vertex. -/
lemma sumZeroTriples_edgeDegree_sdiff_le [NeZero n] (rho : ZMod n → V) (hrhoU : ∀ z, rho z ∈ U)
    (hrho : ∀ z, psi (rho z) = z) (hinj : ∀ x ∈ U, ∀ y ∈ U, psi x = psi y → x = y) (v : V) :
    edgeDegree (U.innerEdges \ familyEdges (sumZeroTriples n U psi)) v ≤ 3 := by
  classical
  by_cases hv : v ∈ U
  · -- the uncovered edges at `v` all go to the (at most three) exceptional partners
    set Bad : Finset V := {u ∈ U | psi u = -(2 * psi v) ∨ 2 * psi u = -psi v}
    have hcardBad : #Bad ≤ 3 := card_exceptional_le hinj v
    have hsub : {e ∈ U.innerEdges \ familyEdges (sumZeroTriples n U psi) | v ∈ e}
        ⊆ Bad.image fun u => s(v, u) := by
      intro e he
      rw [Finset.mem_filter, Finset.mem_sdiff] at he
      obtain ⟨⟨hein, henot⟩, hve⟩ := he
      induction e with
      | h a b =>
        rw [Finset.mem_innerEdges] at hein
        have hab : a ≠ b := by
          intro h; exact hein.2 (by simp [h])
        have haU : a ∈ U := hein.1 a (by simp)
        have hbU : b ∈ U := hein.1 b (by simp)
        have key : ∀ x y : V, x ∈ U → y ∈ U → x ≠ y → s(x, y) ∉
            familyEdges (sumZeroTriples n U psi) → psi y = -(2 * psi x) ∨ 2 * psi y = -psi x := by
          intro x y hx hy hxy hcov
          by_contra hcon
          push Not at hcon
          exact hcov (mem_familyEdges_sumZeroTriples rho hrhoU hrho hx hy hxy hcon.1 hcon.2)
        rcases Sym2.mem_iff.1 hve with rfl | rfl
        · refine Finset.mem_image.2 ⟨b, ?_, rfl⟩
          exact Finset.mem_filter.2 ⟨hbU, key v b hv hbU hab henot⟩
        · refine Finset.mem_image.2 ⟨a, ?_, ?_⟩
          · refine Finset.mem_filter.2 ⟨haU, key v a hv haU (Ne.symm hab) ?_⟩
            rw [Sym2.eq_swap]; exact henot
          · rw [Sym2.eq_swap]
    calc edgeDegree (U.innerEdges \ familyEdges (sumZeroTriples n U psi)) v
        ≤ #(Bad.image fun u => s(v, u)) := Finset.card_le_card hsub
      _ ≤ #Bad := Finset.card_image_le
      _ ≤ 3 := hcardBad
  · -- no edge inside `U` meets `v`
    have hempty : {e ∈ U.innerEdges \ familyEdges (sumZeroTriples n U psi) | v ∈ e} = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro e he hve
      rw [Finset.mem_sdiff] at he
      exact hv ((Finset.mem_innerEdges.1 he.1).1 v hve)
    simp [edgeDegree, hempty]

/-! ### The near-perfect triangle packing of a clique -/

/-- **A near-perfect triangle packing of a complete graph.**

For every finite set `U` of vertices there is a family of pairwise edge-disjoint triangles inside
`U` which leaves at most three uncovered edges at every vertex.  (For `|U| ≡ 1, 3 [MOD 6]` a
Steiner triple system leaves no uncovered edge at all; the sum-zero construction used here is
uniform in `|U|` and gives the bound `3` in all cases.) -/
theorem exists_triangle_packing_clique (U : Finset V) :
    ∃ P : Finset (Finset V),
      (∀ t ∈ P, #t = 3) ∧ (∀ t ∈ P, t ⊆ U) ∧
      (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint t.innerEdges t'.innerEdges) ∧
      (∀ v : V, edgeDegree (U.innerEdges \ familyEdges P) v ≤ 3) := by
  classical
  rcases Nat.eq_zero_or_pos #U with hU | hU
  · -- `U` is empty: there is nothing to cover
    refine ⟨∅, by simp, by simp, by simp, fun v => ?_⟩
    have hUe : U = ∅ := Finset.card_eq_zero.1 hU
    simp [hUe, Finset.innerEdges, edgeDegree]
  · have hU_ne : #U ≠ 0 := by omega
    let _ : NeZero #U := ⟨hU_ne⟩
    set n := #U
    have hcard : Fintype.card {x // x ∈ U} = Fintype.card (ZMod n) := by
      rw [Fintype.card_coe, ZMod.card]
    let e : {x // x ∈ U} ≃ ZMod n := Fintype.equivOfCardEq hcard
    let psi : V → ZMod n := fun x => if h : x ∈ U then e ⟨x, h⟩ else 0
    let rho : ZMod n → V := fun z => (e.symm z : V)
    have hrhoU : ∀ z, rho z ∈ U := fun z => (e.symm z).2
    have hpsi : ∀ (x : V) (h : x ∈ U), psi x = e ⟨x, h⟩ := by
      intro x h; simp [psi, h]
    have hrho : ∀ z, psi (rho z) = z := by
      intro z
      rw [hpsi _ (hrhoU z)]
      simp [rho]
    have hinj : ∀ x ∈ U, ∀ y ∈ U, psi x = psi y → x = y := by
      intro x hx y hy hxy
      rw [hpsi x hx, hpsi y hy] at hxy
      exact congrArg Subtype.val (e.injective hxy)
    refine ⟨sumZeroTriples n U psi, ?_, ?_, sumZeroTriples_disjoint hinj, ?_⟩
    · intro t ht; exact (mem_sumZeroTriples.1 ht).2.1
    · intro t ht; exact (mem_sumZeroTriples.1 ht).1
    · intro v; exact sumZeroTriples_edgeDegree_sdiff_le rho hrhoU hrho hinj v

end SumZeroTriangles
