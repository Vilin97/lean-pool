/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card

/-!
# Doubly regular tournaments

A *tournament* on an index type `ι` is an orientation of the complete graph, encoded here as a
function `Arc : ι → ι → Bool`.  This file sets up the neighbourhood `Finset`s of such an `Arc`
and the parametrised predicate saying that it is *doubly regular*.

Main definitions:

* `IsTournament Arc` — `Arc` has no loops and joins any two distinct vertices by exactly one
  arc;
* `outNbrs Arc i` / `inNbrs Arc i` — the out- and in-neighbours of `i`;
* `commonOut Arc i j` / `commonIn Arc i j` — their pairwise intersections;
* `middles Arc u v` — the vertices `l` with `u → l → v`;
* `IsDRTournamentWith Arc d t` — `Arc` is a doubly regular tournament with out-degree `d` and
  with `t` common out-neighbours and `t` common in-neighbours for every pair of distinct
  vertices.

`IsDRTournamentWith` follows the shape of Mathlib's `SimpleGraph.IsSRGWith`: the arc relation
and the numeric parameters are *arguments*, not fields, so that lemmas stated about a bare
`Arc` can consume it without being rephrased.  The material is organised by hypothesis
strength: first what needs no finiteness, then what needs `Fintype ι`, then what needs
`DecidableEq ι` as well.

This file corresponds to Section 2 of `bs_lambda.txt`; the Paley tournament realising these
axioms is built in `BSLambda/Paley/Tournament.lean`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda

open Finset

variable {ι : Type*}

/-- `IsTournament Arc`: the relation `Arc` orients the complete graph on `ι`, i.e. there are no
loops and any two distinct vertices are joined by exactly one arc. -/
structure IsTournament (Arc : ι → ι → Bool) : Prop where
  /-- There is no arc from a vertex to itself. -/
  arc_self : ∀ i, Arc i i = false
  /-- Distinct vertices are joined by exactly one arc. -/
  arc_eq_not_arc : ∀ {i j}, i ≠ j → Arc i j = !Arc j i

namespace IsTournament

variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h

/-- The endpoints of an arc are distinct. -/
theorem ne_of_arc (hij : Arc i j) : i ≠ j := by
  rintro rfl
  simp [h.arc_self] at hij

/-- The endpoints of an arc are distinct.  The primed name follows Mathlib's `LT.lt.ne'`
convention: the conclusion is `j ≠ i`, the reverse of `BSLambda.IsTournament.ne_of_arc`. -/
theorem ne_of_arc' (hij : Arc i j) : j ≠ i := (h.ne_of_arc hij).symm

/-- Asymmetry in the `Bool`-equation form consumed by the certificate-conflict lemmas:
an arc `i → j` forces `Arc j i = false`. -/
theorem arc_eq_false_of_arc (hij : Arc i j) : Arc j i = false := by
  rw [h.arc_eq_not_arc (h.ne_of_arc hij).symm, hij, Bool.not_true]

/-- The arc relation of a tournament is asymmetric. -/
theorem arc_asymm (hij : Arc i j) : ¬ Arc j i :=
  Bool.eq_false_iff.mp (h.arc_eq_false_of_arc hij)

/-- Any two distinct vertices of a tournament are joined by an arc. -/
theorem arc_or_arc (hij : i ≠ j) : Arc i j ∨ Arc j i := by
  cases hb : Arc j i <;> simp [h.arc_eq_not_arc hij, hb]

/-- The `Bool`-equation form of `BSLambda.IsTournament.arc_or_arc`: if `j` does not beat `i`
then `i` beats `j`. -/
theorem arc_of_not_arc (hij : i ≠ j) (hji : Arc j i = false) : Arc i j := by
  rw [h.arc_eq_not_arc hij, hji, Bool.not_false]

end IsTournament

variable [Fintype ι]

/-- The out-neighbours of `i`: the vertices `j` with an arc `i → j`. -/
def outNbrs (Arc : ι → ι → Bool) (i : ι) : Finset ι := {j | Arc i j}

/-- The in-neighbours of `i`: the vertices `j` with an arc `j → i`. -/
def inNbrs (Arc : ι → ι → Bool) (i : ι) : Finset ι := {j | Arc j i}

section Nbrs
variable {Arc : ι → ι → Bool} {i j : ι}

@[simp] theorem mem_outNbrs : j ∈ outNbrs Arc i ↔ Arc i j := by simp [outNbrs]

@[simp] theorem mem_inNbrs : j ∈ inNbrs Arc i ↔ Arc j i := by simp [inNbrs]

variable (Arc) in
/-- Counting the arcs of `Arc` by tail and by head. -/
theorem sum_card_outNbrs_eq_sum_card_inNbrs :
    ∑ x, (outNbrs Arc x).card = ∑ x, (inNbrs Arc x).card := by
  simp only [outNbrs, inNbrs, card_filter]
  exact sum_comm

/-- The out-neighbourhood and the in-neighbourhood of a vertex are disjoint. -/
theorem IsTournament.disjoint_outNbrs_inNbrs (h : IsTournament Arc) (v : ι) :
    Disjoint (outNbrs Arc v) (inNbrs Arc v) :=
  disjoint_left.2 fun _ hx hx' ↦ h.arc_asymm (mem_outNbrs.1 hx) (mem_inNbrs.1 hx')

end Nbrs

variable [DecidableEq ι]

/-- The common out-neighbours of `i` and `j`. -/
def commonOut (Arc : ι → ι → Bool) (i j : ι) : Finset ι := outNbrs Arc i ∩ outNbrs Arc j

/-- The common in-neighbours of `i` and `j`. -/
def commonIn (Arc : ι → ι → Bool) (i j : ι) : Finset ι := inNbrs Arc i ∩ inNbrs Arc j

/-- The middle vertices of the arc `u → v`: those `l` with `u → l → v`. -/
def middles (Arc : ι → ι → Bool) (u v : ι) : Finset ι := outNbrs Arc u ∩ inNbrs Arc v

section Common
variable {Arc : ι → ι → Bool} {i j l u v : ι}

@[simp] theorem mem_commonOut : l ∈ commonOut Arc i j ↔ Arc i l ∧ Arc j l := by simp [commonOut]

@[simp] theorem mem_commonIn : l ∈ commonIn Arc i j ↔ Arc l i ∧ Arc l j := by simp [commonIn]

@[simp] theorem mem_middles : l ∈ middles Arc u v ↔ Arc u l ∧ Arc l v := by simp [middles]

variable (Arc u) in
/-- Counting the arcs inside the out-neighbourhood of `u` by tail and by head: a pure
double-counting identity, with no regularity assumption on `Arc`. -/
theorem sum_card_commonOut_eq_sum_card_middles :
    ∑ y ∈ outNbrs Arc u, (commonOut Arc u y).card
      = ∑ y ∈ outNbrs Arc u, (middles Arc u y).card := by
  simp only [commonOut, middles, ← filter_mem_eq_inter, card_filter, mem_outNbrs, mem_inNbrs]
  exact sum_comm

namespace IsTournament

variable (h : IsTournament Arc)
include h

/-- The out- and in-neighbours of `v` are exactly the vertices other than `v`. -/
theorem outNbrs_union_inNbrs (v : ι) : outNbrs Arc v ∪ inNbrs Arc v = univ.erase v := by
  ext x
  simp only [mem_union, mem_outNbrs, mem_inNbrs, mem_erase, mem_univ, and_true]
  exact ⟨fun hx ↦ hx.elim (fun hx ↦ (h.ne_of_arc hx).symm) h.ne_of_arc,
    fun hx ↦ h.arc_or_arc hx.symm⟩

omit [DecidableEq ι] in
/-- Out-neighbours and in-neighbours of a vertex partition the remaining vertices. -/
theorem card_outNbrs_add_card_inNbrs (v : ι) :
    (outNbrs Arc v).card + (inNbrs Arc v).card + 1 = Fintype.card ι := by
  classical
  rw [← card_univ, ← card_erase_add_one (mem_univ v), ← h.outNbrs_union_inNbrs v,
    card_union_of_disjoint (h.disjoint_outNbrs_inNbrs v)]

end IsTournament

end Common

/-- `IsDRTournamentWith Arc d t`: `Arc` is a *doubly regular tournament* — a tournament in which
every vertex has out-degree `d`, and every two distinct vertices have `t` common out-neighbours
and `t` common in-neighbours. (Section 2 of `bs_lambda.txt`.) -/
structure IsDRTournamentWith (Arc : ι → ι → Bool) (d t : ℕ) : Prop extends IsTournament Arc where
  /-- Every vertex has out-degree `d`. -/
  card_outNbrs : ∀ i, (outNbrs Arc i).card = d
  /-- Distinct vertices have `t` common out-neighbours. -/
  card_commonOut : ∀ {i j}, i ≠ j → (commonOut Arc i j).card = t
  /-- Distinct vertices have `t` common in-neighbours. -/
  card_commonIn : ∀ {i j}, i ≠ j → (commonIn Arc i j).card = t

namespace IsDRTournamentWith

variable {Arc : ι → ι → Bool} {d t : ℕ} (h : IsDRTournamentWith Arc d t) {u v : ι}
include h

/-- Every vertex of a doubly regular tournament has in-degree `d` as well. -/
theorem card_inNbrs (i : ι) : (inNbrs Arc i).card = d := by
  have hall (x : ι) : (inNbrs Arc x).card = (inNbrs Arc i).card := by
    have h1 := h.card_outNbrs_add_card_inNbrs x
    have h2 := h.card_outNbrs_add_card_inNbrs i
    rw [h.card_outNbrs] at h1 h2
    omega
  have hsum := sum_card_outNbrs_eq_sum_card_inNbrs Arc
  rw [sum_const_nat fun x _ ↦ h.card_outNbrs x, sum_const_nat fun x _ ↦ hall x, card_univ] at hsum
  exact (Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.2 ⟨i⟩) hsum).symm

/-- A doubly regular tournament on a nonempty `ι` has `2 * d + 1` vertices. -/
theorem card_eq_two_mul_add_one [Nonempty ι] : Fintype.card ι = 2 * d + 1 := by
  have hi := h.card_outNbrs_add_card_inNbrs (Classical.arbitrary ι)
  rw [h.card_outNbrs, h.card_inNbrs] at hi
  omega

/-- Along an arc `u → v` the out-neighbours of `u` split into `v` itself, the middles of the
arc, and the `t` common out-neighbours of `u` and `v`. -/
theorem card_middles_add_add_one (huv : Arc u v) : (middles Arc u v).card + t + 1 = d := by
  have hdisj : Disjoint (middles Arc u v) (commonOut Arc u v) :=
    disjoint_left.2 fun _ hx hx' ↦ h.arc_asymm (mem_middles.1 hx).2 (mem_commonOut.1 hx').2
  have hsplit : outNbrs Arc u = insert v (middles Arc u v ∪ commonOut Arc u v) := by
    ext x
    simp only [mem_insert, mem_union, mem_middles, mem_commonOut, mem_outNbrs]
    constructor
    · exact fun hx ↦ (eq_or_ne x v).imp id fun hne ↦ (h.arc_or_arc hne).imp (⟨hx, ·⟩) (⟨hx, ·⟩)
    · rintro (rfl | ⟨hx, -⟩ | ⟨hx, -⟩)
      exacts [huv, hx, hx]
  rw [← h.card_outNbrs u, hsplit, card_insert_of_notMem (by simp [h.arc_self]),
    card_union_of_disjoint hdisj, h.card_commonOut (h.ne_of_arc huv)]

/-- A doubly regular tournament with at least two vertices has positive out-degree. -/
theorem d_pos [Nontrivial ι] : 0 < d := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  obtain hb | hb := h.arc_or_arc hab
  exacts [(card_pos.2 ⟨b, mem_outNbrs.2 hb⟩).trans_eq (h.card_outNbrs a),
    (card_pos.2 ⟨a, mem_outNbrs.2 hb⟩).trans_eq (h.card_outNbrs b)]

/-- A doubly regular tournament with at least two vertices satisfies `d = 2 * t + 1`; in
particular `d - 1 - t = t`. -/
theorem d_eq_two_mul_t_add_one [Nontrivial ι] : d = 2 * t + 1 := by
  obtain ⟨x⟩ : Nonempty ι := inferInstance
  obtain ⟨w, hw⟩ : (outNbrs Arc x).Nonempty := by
    rw [← card_pos, h.card_outNbrs x]
    exact h.d_pos
  have hall (y : ι) (hy : y ∈ outNbrs Arc x) :
      (middles Arc x y).card = (middles Arc x w).card := by
    have h1 := h.card_middles_add_add_one (mem_outNbrs.1 hy)
    have h2 := h.card_middles_add_add_one (mem_outNbrs.1 hw)
    omega
  have hL : ∑ y ∈ outNbrs Arc x, (commonOut Arc x y).card = d * t := by
    rw [sum_const_nat fun y hy ↦ h.card_commonOut (h.ne_of_arc (mem_outNbrs.1 hy)),
      h.card_outNbrs x]
  have hR : ∑ y ∈ outNbrs Arc x, (middles Arc x y).card = d * (middles Arc x w).card := by
    rw [sum_const_nat hall, h.card_outNbrs x]
  have hm := h.card_middles_add_add_one (mem_outNbrs.1 hw)
  have := Nat.eq_of_mul_eq_mul_left h.d_pos
    (hL.symm.trans ((sum_card_commonOut_eq_sum_card_middles Arc x).trans hR))
  omega

/-- In a doubly regular tournament with at least two vertices, every arc `u → v` has exactly
`t` middle vertices. -/
theorem card_middles [Nontrivial ι] (huv : Arc u v) : (middles Arc u v).card = t := by
  have h1 := h.card_middles_add_add_one huv
  have h2 := h.d_eq_two_mul_t_add_one
  omega

end IsDRTournamentWith

end BSLambda
