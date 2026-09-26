/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.Framework
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The edge-reduction construction

This file formalizes the bipartite graph `B(H)` used in Lemma 4.1 of the draft.  An edge between
the two copies of the vertex set records either equality or adjacency in `H`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

variable {V : Type u}

/-- Equality or adjacency in a simple graph (the reflexive closure of adjacency). -/
def Linked (H : SimpleGraph V) (x y : V) : Prop :=
  x = y ∨ H.Adj x y

lemma linked_refl (H : SimpleGraph V) (x : V) : Linked H x x :=
  Or.inl rfl

lemma linked_symm {H : SimpleGraph V} {x y : V} : Linked H x y → Linked H y x := by
  rintro (rfl | h)
  · exact linked_refl H x
  · exact Or.inr h.symm

/-- The graph `B(H)` from the draft.  Its two parts are the two summands of `V ⊕ V`. -/
def bipartiteExpansion (H : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj
    | .inl x, .inr y => Linked H x y
    | .inr y, .inl x => Linked H x y
    | _, _ => False
  symm.symm _ _ := by
    grind [Linked, SimpleGraph.adj_comm]
  loopless.irrefl _ := by
    grind

@[simp] lemma bipartiteExpansion_adj_inl_inr (H : SimpleGraph V) (x y : V) :
    (bipartiteExpansion H).Adj (.inl x) (.inr y) ↔ Linked H x y :=
  Iff.rfl

@[simp] lemma bipartiteExpansion_adj_inr_inl (H : SimpleGraph V) (x y : V) :
    (bipartiteExpansion H).Adj (.inr y) (.inl x) ↔ Linked H x y :=
  Iff.rfl

@[simp] lemma bipartiteExpansion_not_adj_inl_inl (H : SimpleGraph V) (x y : V) :
    ¬ (bipartiteExpansion H).Adj (.inl x) (.inl y) := by
  simp [bipartiteExpansion]

@[simp] lemma bipartiteExpansion_not_adj_inr_inr (H : SimpleGraph V) (x y : V) :
    ¬ (bipartiteExpansion H).Adj (.inr x) (.inr y) := by
  simp [bipartiteExpansion]

/-- The edge of `B(H)` represented in the draft by `[x,y]`. -/
def bipartiteEdge (H : SimpleGraph V) (x y : V) (hxy : Linked H x y) :
    (bipartiteExpansion H).edgeSet :=
  ⟨s(.inl x, .inr y), by simpa [SimpleGraph.mem_edgeSet] using hxy⟩

@[simp] lemma bipartiteEdge_val (H : SimpleGraph V) (x y : V) (hxy : Linked H x y) :
    (bipartiteEdge H x y hxy : Sym2 (V ⊕ V)) = s(.inl x, .inr y) :=
  rfl

lemma setOf_linked_eq_insert_neighborSet (H : SimpleGraph V) (x : V) :
    {y : V | Linked H x y} = insert x (H.neighborSet x) := by
  ext y
  simp [Linked, eq_comm]

lemma neighborSet_bipartiteExpansion_inl (H : SimpleGraph V) (x : V) :
    (bipartiteExpansion H).neighborSet (.inl x) =
      Sum.inr '' insert x (H.neighborSet x) := by
  ext y
  cases y <;> simp [SimpleGraph.mem_neighborSet, bipartiteExpansion, Linked, eq_comm]

lemma neighborSet_bipartiteExpansion_inr (H : SimpleGraph V) (x : V) :
    (bipartiteExpansion H).neighborSet (.inr x) =
      Sum.inl '' insert x (H.neighborSet x) := by
  ext y
  cases y <;> simp [SimpleGraph.mem_neighborSet, bipartiteExpansion, Linked, eq_comm,
    SimpleGraph.adj_comm]

lemma ncard_neighborSet_bipartiteExpansion_inl [Finite V]
    (H : SimpleGraph V) (x : V) :
    ((bipartiteExpansion H).neighborSet (.inl x)).ncard =
      (H.neighborSet x).ncard + 1 := by
  rw [neighborSet_bipartiteExpansion_inl, Set.ncard_image_of_injective _ Sum.inr_injective,
    Set.ncard_insert_of_notMem]
  simp

lemma ncard_neighborSet_bipartiteExpansion_inr [Finite V]
    (H : SimpleGraph V) (x : V) :
    ((bipartiteExpansion H).neighborSet (.inr x)).ncard =
      (H.neighborSet x).ncard + 1 := by
  rw [neighborSet_bipartiteExpansion_inr, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_insert_of_notMem]
  simp

/-- `B(H)` raises the maximum-degree bound by exactly one. -/
lemma maxDegreeLE_bipartiteExpansion [Finite V] {H : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE H d) : MaxDegreeLE (bipartiteExpansion H) (d + 1) := by
  intro x
  cases x with
  | inl x =>
      rw [ncard_neighborSet_bipartiteExpansion_inl]
      exact Nat.add_le_add_right (hdegree x) 1
  | inr x =>
      rw [ncard_neighborSet_bipartiteExpansion_inr]
      exact Nat.add_le_add_right (hdegree x) 1

/-- If every vertex of `H` has degree `Delta`, then the paper's graph `B(H)` has exactly
`|V(H)| * (Delta + 1)` edges. -/
theorem ncard_edgeSet_bipartiteExpansion_of_regular [Finite V]
    (H : SimpleGraph V) (Delta : ℕ)
    (hregular : ∀ x, (H.neighborSet x).ncard = Delta) :
    (bipartiteExpansion H).edgeSet.ncard = Nat.card V * (Delta + 1) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let B := bipartiteExpansion H
  let : DecidableRel B.Adj := Classical.decRel B.Adj
  have hBdegree : ∀ v, B.degree v = Delta + 1 := by
    intro v
    rw [← B.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    cases v with
    | inl x => exact (ncard_neighborSet_bipartiteExpansion_inl H x).trans (congrArg (· + 1)
        (hregular x))
    | inr x => exact (ncard_neighborSet_bipartiteExpansion_inr H x).trans (congrArg (· + 1)
        (hregular x))
  have hsum : Fintype.card (V ⊕ V) * (Delta + 1) = 2 * B.edgeFinset.card := by
    simpa [hBdegree] using B.sum_degrees_eq_twice_card_edges
  have htwice : 2 * (Nat.card V * (Delta + 1)) = 2 * B.edgeFinset.card := by
    calc
      2 * (Nat.card V * (Delta + 1)) = Fintype.card (V ⊕ V) * (Delta + 1) := by
        rw [Nat.card_eq_fintype_card]
        simp [Fintype.card_sum, two_mul, add_mul]
      _ = 2 * B.edgeFinset.card := hsum
  have hedge : B.edgeFinset.card = Nat.card V * (Delta + 1) := by
    exact Nat.mul_left_cancel zero_lt_two htwice.symm
  calc
    B.edgeSet.ncard = Nat.card B.edgeSet := (Nat.card_coe_set_eq _).symm
    _ = B.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, ← B.edgeFinset_card]
    _ = Nat.card V * (Delta + 1) := hedge

/-- Every edge of `B(H)` has a unique orientation from the left part to the right part. -/
lemma exists_eq_bipartiteEdge (H : SimpleGraph V) (e : (bipartiteExpansion H).edgeSet) :
    ∃ x y, ∃ hxy : Linked H x y, e = bipartiteEdge H x y hxy := by
  rcases e with ⟨e, he⟩
  induction e with
  | _ u v =>
      cases u with
      | inl x =>
          cases v with
          | inl y => simp [SimpleGraph.mem_edgeSet, bipartiteExpansion] at he
          | inr y =>
              refine ⟨x, y, ?_, ?_⟩
              · simpa [SimpleGraph.mem_edgeSet, bipartiteExpansion] using he
              · rfl
      | inr y =>
          cases v with
          | inl x =>
              refine ⟨x, y, ?_, ?_⟩
              · simpa [SimpleGraph.mem_edgeSet, bipartiteExpansion] using he
              · apply Subtype.ext
                simp [bipartiteEdge]
          | inr x => simp [SimpleGraph.mem_edgeSet, bipartiteExpansion] at he

/-- Two represented edges with the same left endpoint have line-graph distance at most one. -/
lemma lineGraph_edist_bipartiteEdge_le_one_of_left
    (H : SimpleGraph V) (a b c : V) (hab : Linked H a b) (hac : Linked H a c) :
    (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a b hab) (bipartiteEdge H a c hac) ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases hEq : bipartiteEdge H a b hab = bipartiteEdge H a c hac
  · exact Or.inr hEq
  · exact Or.inl <| SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨hEq, .inl a, by simp [bipartiteEdge], by simp [bipartiteEdge]⟩

/-- Two represented edges with the same right endpoint have line-graph distance at most one. -/
lemma lineGraph_edist_bipartiteEdge_le_one_of_right
    (H : SimpleGraph V) (a b c : V) (hac : Linked H a c) (hbc : Linked H b c) :
    (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a c hac) (bipartiteEdge H b c hbc) ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases hEq : bipartiteEdge H a c hac = bipartiteEdge H b c hbc
  · exact Or.inr hEq
  · exact Or.inl <| SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨hEq, .inr c, by simp [bipartiteEdge], by simp [bipartiteEdge]⟩

/-- A route permits stationary steps as well as graph edges.  It is indexed by its exact length;
this is the formal counterpart of the padded sequences in the paper's proof of Lemma 4.1. -/
inductive Route (H : SimpleGraph V) : V → V → ℕ → Type u
  | nil (x : V) : Route H x x 0
  | cons {x y z : V} {n : ℕ} (hxy : Linked H x y) (tail : Route H y z n) :
      Route H x z n.succ

namespace Route

/-- Regard a graph walk as a route allowing both adjacency and stationary steps. -/
def ofWalk (H : SimpleGraph V) {x y : V} : (p : H.Walk x y) → Route H x y p.length
  | .nil => .nil x
  | .cons h p => .cons (Or.inr h) (ofWalk H p)

/-- The route of the specified length that stays at one vertex. -/
def stay (H : SimpleGraph V) (x : V) : (n : ℕ) → Route H x x n
  | 0 => .nil x
  | n + 1 => .cons (linked_refl H x) (stay H x n)

/-- Concatenate routes.  The length index is written in this order so the defining equations
reduce without arithmetic casts when recursing through the first route. -/
def append {H : SimpleGraph V} {x y z : V} {m n : ℕ} :
    Route H x y m → Route H y z n → Route H x z (n + m)
  | .nil _, q => q
  | .cons h p, q => .cons h (append p q)

/-- Pad an ordinary graph walk by stationary steps to any prescribed larger length. -/
def padWalk (H : SimpleGraph V) {x y : V} (p : H.Walk x y) (k : ℕ)
    (hp : p.length ≤ k) : Route H x y k := by
  have hlen : (k - p.length) + p.length = k := Nat.sub_add_cancel hp
  exact hlen ▸ append (ofWalk H p) (stay H y (k - p.length))

end Route

/-- Compute both alternating edge endpoints by structural recursion on the route.
The two functions record which coordinate is replaced first. -/
def zigEndpoints (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n) :
    ((a : V) → Linked H a x → (bipartiteExpansion H).edgeSet) ×
      ((b : V) → Linked H x b → (bipartiteExpansion H).edgeSet) :=
  match p with
  | .nil _ => ⟨fun a ha ↦ bipartiteEdge H a x ha, fun b hb ↦ bipartiteEdge H x b hb⟩
  | .cons h tail =>
      let endpoints := zigEndpoints H tail
      ⟨fun _ _ ↦ endpoints.2 x (linked_symm h), fun _ _ ↦ endpoints.1 x h⟩

/-- Follow a route by first replacing the left coordinate of a represented bipartite edge. -/
def zigFirst (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n)
    (a : V) (ha : Linked H a x) : (bipartiteExpansion H).edgeSet :=
  (zigEndpoints H p).1 a ha

/-- Follow a route by first replacing the right coordinate of a represented bipartite edge. -/
def zigSecond (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n)
    (b : V) (hb : Linked H x b) : (bipartiteExpansion H).edgeSet :=
  (zigEndpoints H p).2 b hb

theorem zig_terminal (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n) :
    (∀ a (ha : Linked H a x),
      (Even n → ∃ a', ∃ ha' : Linked H a' y,
        zigFirst H p a ha = bipartiteEdge H a' y ha') ∧
      (Odd n → ∃ b', ∃ hb' : Linked H y b',
        zigFirst H p a ha = bipartiteEdge H y b' hb')) ∧
    (∀ b (hb : Linked H x b),
      (Even n → ∃ b', ∃ hb' : Linked H y b',
        zigSecond H p b hb = bipartiteEdge H y b' hb') ∧
      (Odd n → ∃ a', ∃ ha' : Linked H a' y,
        zigSecond H p b hb = bipartiteEdge H a' y ha')) := by
  induction p with
  | nil x =>
      constructor
      · intro a ha
        constructor
        · intro _
          exact ⟨a, ha, rfl⟩
        · intro hn
          simp at hn
      · intro b hb
        constructor
        · intro _
          exact ⟨b, hb, rfl⟩
        · intro hn
          simp at hn
  | @cons x x' y n hxx' tail ih =>
      constructor
      · intro a ha
        constructor
        · intro hn
          have hn' : Odd n := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn)
          simpa [zigFirst, zigSecond, zigEndpoints] using (ih.2 x (linked_symm hxx')).2 hn'
        · intro hn
          have hn' : Even n := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn)
          simpa [zigFirst, zigSecond, zigEndpoints] using (ih.2 x (linked_symm hxx')).1 hn'
      · intro b hb
        constructor
        · intro hn
          have hn' : Odd n := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn)
          simpa [zigFirst, zigSecond, zigEndpoints] using (ih.1 x hxx').2 hn'
        · intro hn
          have hn' : Even n := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn)
          simpa [zigFirst, zigSecond, zigEndpoints] using (ih.1 x hxx').1 hn'

theorem zigFirst_of_even (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (a : V) (ha : Linked H a x) (hn : Even n) :
    ∃ a', ∃ ha' : Linked H a' y, zigFirst H p a ha = bipartiteEdge H a' y ha' :=
  ((zig_terminal H p).1 a ha).1 hn

theorem zigFirst_of_odd (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (a : V) (ha : Linked H a x) (hn : Odd n) :
    ∃ b', ∃ hb' : Linked H y b', zigFirst H p a ha = bipartiteEdge H y b' hb' :=
  ((zig_terminal H p).1 a ha).2 hn

theorem zigSecond_of_even (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (b : V) (hb : Linked H x b) (hn : Even n) :
    ∃ b', ∃ hb' : Linked H y b', zigSecond H p b hb = bipartiteEdge H y b' hb' :=
  ((zig_terminal H p).2 b hb).1 hn

theorem zigSecond_of_odd (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (b : V) (hb : Linked H x b) (hn : Odd n) :
    ∃ a', ∃ ha' : Linked H a' y, zigSecond H p b hb = bipartiteEdge H a' y ha' :=
  ((zig_terminal H p).2 b hb).2 hn

/-- Both alternating coordinate routes cost no more than one line-graph step per route step. -/
theorem edist_zig_le (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n) :
    (∀ a (ha : Linked H a x),
      (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a x ha) (zigFirst H p a ha) ≤ (n : ℕ∞)) ∧
    (∀ b (hb : Linked H x b),
      (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H x b hb) (zigSecond H p b hb) ≤ (n : ℕ∞)) := by
  induction p with
  | nil x =>
      constructor <;> intro z hz <;> simp [zigFirst, zigSecond, zigEndpoints]
  | @cons x x' y n hxx' tail ih =>
      constructor
      · intro a ha
        calc
          (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H a x ha) (zigFirst H (.cons hxx' tail) a ha)
              ≤ (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H a x ha) (bipartiteEdge H x' x (linked_symm hxx')) +
                (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H x' x (linked_symm hxx'))
                  (zigSecond H tail x (linked_symm hxx')) :=
            SimpleGraph.edist_triangle
          _ ≤ 1 + (n : ℕ∞) := add_le_add
            (lineGraph_edist_bipartiteEdge_le_one_of_right H a x' x ha (linked_symm hxx'))
            (ih.2 x (linked_symm hxx'))
          _ = ((n + 1 : ℕ) : ℕ∞) := by simp [add_comm]
      · intro b hb
        calc
          (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H x b hb) (zigSecond H (.cons hxx' tail) b hb)
              ≤ (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H x b hb) (bipartiteEdge H x x' hxx') +
                (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H x x' hxx') (zigFirst H tail x hxx') :=
            SimpleGraph.edist_triangle
          _ ≤ 1 + (n : ℕ∞) := add_le_add
            (lineGraph_edist_bipartiteEdge_le_one_of_left H x b x' hb hxx')
            (ih.1 x hxx')
          _ = ((n + 1 : ℕ) : ℕ∞) := by simp [add_comm]

theorem edist_zigFirst_le (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (a : V) (ha : Linked H a x) :
    (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a x ha) (zigFirst H p a ha) ≤ (n : ℕ∞) :=
  (edist_zig_le H p).1 a ha

theorem edist_zigSecond_le (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (b : V) (hb : Linked H x b) :
    (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H x b hb) (zigSecond H p b hb) ≤ (n : ℕ∞) :=
  (edist_zig_le H p).2 b hb

/-- A diameter bound in `H` supplies an exact-length padded route between every two vertices. -/
lemma nonempty_route_of_ediam_le (H : SimpleGraph V) (k : ℕ)
    (hdiam : H.ediam ≤ (k : ℕ∞)) (x y : V) : Nonempty (Route H x y k) := by
  have hdist : H.edist x y ≤ (k : ℕ∞) := SimpleGraph.edist_le_ediam.trans hdiam
  have hfinite : H.edist x y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top k) hdist
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlength : p.length ≤ k := by
    rw [← hp] at hdist
    exact_mod_cast hdist
  exact ⟨Route.padWalk H p k hlength⟩

/-- Pointwise distance form of Lemma 4.1. -/
lemma lineGraph_edist_bipartiteExpansion_le (H : SimpleGraph V) (k : ℕ)
    (hdiam : H.ediam ≤ (k : ℕ∞))
    (e f : (bipartiteExpansion H).edgeSet) :
    (bipartiteExpansion H).lineGraph.edist e f ≤ ((k + 1 : ℕ) : ℕ∞) := by
  obtain ⟨a, b, hab, rfl⟩ := exists_eq_bipartiteEdge H e
  obtain ⟨c, d, hcd, rfl⟩ := exists_eq_bipartiteEdge H f
  by_cases hk : Even k
  · obtain ⟨p⟩ := nonempty_route_of_ediam_le H k hdiam b d
    obtain ⟨u, hud, hterminal⟩ := zigFirst_of_even H p a hab hk
    calc
      (bipartiteExpansion H).lineGraph.edist
          (bipartiteEdge H a b hab) (bipartiteEdge H c d hcd)
          ≤ (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H a b hab) (zigFirst H p a hab) +
            (bipartiteExpansion H).lineGraph.edist
              (zigFirst H p a hab) (bipartiteEdge H c d hcd) :=
        SimpleGraph.edist_triangle
      _ ≤ (k : ℕ∞) + 1 := add_le_add (edist_zigFirst_le H p a hab) <| by
        rw [hterminal]
        exact lineGraph_edist_bipartiteEdge_le_one_of_right H u c d hud hcd
      _ = ((k + 1 : ℕ) : ℕ∞) := by simp
  · have hk' : Odd k := Nat.not_even_iff_odd.mp hk
    obtain ⟨p⟩ := nonempty_route_of_ediam_le H k hdiam b c
    obtain ⟨u, hcu, hterminal⟩ := zigFirst_of_odd H p a hab hk'
    calc
      (bipartiteExpansion H).lineGraph.edist
          (bipartiteEdge H a b hab) (bipartiteEdge H c d hcd)
          ≤ (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H a b hab) (zigFirst H p a hab) +
            (bipartiteExpansion H).lineGraph.edist
              (zigFirst H p a hab) (bipartiteEdge H c d hcd) :=
        SimpleGraph.edist_triangle
      _ ≤ (k : ℕ∞) + 1 := add_le_add (edist_zigFirst_le H p a hab) <| by
        rw [hterminal]
        exact lineGraph_edist_bipartiteEdge_le_one_of_left H c u d hcu hcd
      _ = ((k + 1 : ℕ) : ℕ∞) := by simp

/-- Lemma 4.1 in bounded-diameter form.  This formulation also handles empty vertex and edge
types without adding nonemptiness hypotheses. -/
theorem lemma_4_1_le (H : SimpleGraph V) (k : ℕ) (hdiam : H.ediam ≤ (k : ℕ∞)) :
    (bipartiteExpansion H).lineGraph.ediam ≤ ((k + 1 : ℕ) : ℕ∞) :=
  SimpleGraph.ediam_le_of_edist_le (lineGraph_edist_bipartiteExpansion_le H k hdiam)

/-- Lemma 4.1 exactly as an inequality of extended diameters. -/
theorem lemma_4_1 (H : SimpleGraph V) :
    (bipartiteExpansion H).lineGraph.ediam ≤ H.ediam + 1 := by
  by_cases htop : H.ediam = ⊤
  · simp [htop]
  · have h := lemma_4_1_le H H.ediam.toNat <| by
      rw [ENat.natCast_toNat htop]
    simpa [ENat.natCast_toNat htop] using h

end DegreeDiameter

end MooreBound
