/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the diagonal grid design inside one cluster triple

The deterministic (probability-free) route to `Nibble.AX1.ReducedFamilyResidual` splits each cluster
of a good triple `(U, W, X)` into vertex **sub-blocks** and uses the *diagonal* family of
sub-triples

`(U_{(j+k) mod n}, W_j, X_k)`,  `0 ≤ j, k < n`.

`Nibble.AX1.gridShift_UW_injective` and its companions (`Nibble.GridShiftUnique`) say that each of
the three block-pairs `(U_i, W_j)`, `(U_i, X_k)`, `(W_j, X_k)` occurs **at most once** in this
family.  This file turns that arithmetic statement into the graph-theoretic one the assembly needs:
the `n²` tripartite graphs of the diagonal family are pairwise **edge-disjoint**, which is the
hypothesis `hpair` of `Nibble.AX1.hasNearRegularFamily_of_subTripleDesign`.

* `Nibble.AX1.gridA`, `Nibble.AX1.gridB`, `Nibble.AX1.gridC` — the design as three functions
  `ℕ → Finset V`, indexed by `i < n²` through `j = i / n`, `k = i % n`.
* `Nibble.AX1.gridDesign_pairwise_edgeDisjoint` — **the edge-disjointness of the design**.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude


/-! # GridShiftUnique -/

public section

open Finset

namespace Nibble.AX1

/-- The shift `f(j,k) = (j+k) mod n`. -/
def gridShift (n : ℕ) (j k : Fin n) : ℕ := (j.val + k.val) % n

/-- **The `U`–`W` block pair is used at most once**: `(j,k) ↦ (f(j,k), j)` is injective. -/
theorem gridShift_UW_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (gridShift n p.1 p.2, p.1.val)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [gridShift, Prod.mk.injEq] at h
  obtain ⟨hs, hj⟩ := h
  have hjj : j = j' := Fin.ext hj
  subst hjj
  -- hs : (j + k) % n = (j + k') % n, and k, k' < n ⇒ k = k'
  have hmod : k.val % n = k'.val % n :=
    Nat.ModEq.add_left_cancel' j.val (by simpa [Nat.ModEq] using hs)
  have hk : k.val = k'.val := by
    rwa [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt k'.isLt] at hmod
  exact Prod.ext rfl (Fin.ext hk)

/-- **The `U`–`X` block pair is used at most once**: `(j,k) ↦ (f(j,k), k)` is injective. -/
theorem gridShift_UX_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (gridShift n p.1 p.2, p.2.val)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [gridShift, Prod.mk.injEq] at h
  obtain ⟨hs, hk⟩ := h
  have hkk : k = k' := Fin.ext hk
  subst hkk
  -- hs : (j + k) % n = (j' + k) % n, i.e. (k + j) % n = (k + j') % n after commuting
  have hs' : (k.val + j.val) % n = (k.val + j'.val) % n := by
    rw [Nat.add_comm k.val j.val, Nat.add_comm k.val j'.val]; exact hs
  have hmod : j.val % n = j'.val % n :=
    Nat.ModEq.add_left_cancel' k.val (by simpa [Nat.ModEq] using hs')
  have hj : j.val = j'.val := by
    rwa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at hmod
  exact Prod.ext (Fin.ext hj) rfl

/-- **The `W`–`X` block pair is used at most once**: `(j,k) ↦ (j,k)` is injective (trivial). -/
theorem gridShift_WX_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (p.1.val, p.2.val)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- **Consequence: the diagonal grid labelling is injective** — distinct `(j,k)` give distinct
sub-triples `(f(j,k), j, k)`.  (Immediate from any one of the block-pair injectivities, e.g.
`WX`.) -/
theorem gridShift_label_injective {n : ℕ} :
    Function.Injective (fun p : Fin n × Fin n => (gridShift n p.1 p.2, p.1.val, p.2.val)) := by
  intro p q h
  have : (p.1.val, p.2.val) = (q.1.val, q.2.val) := by
    simpa using congrArg (fun t => (t.2.1, t.2.2)) h
  exact gridShift_WX_injective this

end Nibble.AX1

end


/-! # GridDesign -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The index arithmetic of the diagonal design -/

/-- Two indices below `n²` with the same quotient and remainder mod `n` are equal. -/
theorem eq_of_div_mod_eq {n i i' : ℕ}
    (hdiv : i / n = i' / n) (hmod : i % n = i' % n) : i = i' := by
  have h1 := Nat.div_add_mod i n
  have h2 := Nat.div_add_mod i' n
  rw [hdiv, hmod] at h1
  exact h1.symm.trans h2

/-- The `U`-block index of the `i`-th member of the diagonal design. -/
def gridIdxA (n i : ℕ) : ℕ := (i / n + i % n) % n

/-- The `W`-block index of the `i`-th member of the diagonal design. -/
def gridIdxB (n i : ℕ) : ℕ := i / n

/-- The `X`-block index of the `i`-th member of the diagonal design. -/
def gridIdxC (n i : ℕ) : ℕ := i % n

theorem gridIdxA_lt {n : ℕ} (hn : 0 < n) (i : ℕ) : gridIdxA n i < n :=
  Nat.mod_lt _ hn

theorem gridIdxB_lt {n i : ℕ} (hi : i < n * n) : gridIdxB n i < n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hi
    · exact h
  exact Nat.div_lt_of_lt_mul (by omega)

theorem gridIdxC_lt {n : ℕ} (hn : 0 < n) (i : ℕ) : gridIdxC n i < n :=
  Nat.mod_lt _ hn

/-- **The `U`–`W` block pair is used at most once.** -/
theorem gridIdx_AB_inj {n i i' : ℕ} (hi : i < n * n) (hi' : i' < n * n)
    (hA : gridIdxA n i = gridIdxA n i') (hB : gridIdxB n i = gridIdxB n i') : i = i' := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hi
    · exact h
  refine eq_of_div_mod_eq hB ?_
  -- from `(a + b) % n = (a + b') % n` and `hB : a = a'`
  simp only [gridIdxA, gridIdxB] at hA hB
  rw [hB] at hA
  have h1 : (i' / n + i % n) % n = (i' / n + i' % n) % n := hA
  have hr : i % n < n := Nat.mod_lt _ hn
  have hr' : i' % n < n := Nat.mod_lt _ hn
  have h2 : (i % n) % n = (i' % n) % n :=
    Nat.ModEq.add_left_cancel' (i' / n) (by simpa [Nat.ModEq] using h1)
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h2

/-- **The `U`–`X` block pair is used at most once.** -/
theorem gridIdx_AC_inj {n i i' : ℕ} (hi : i < n * n) (hi' : i' < n * n)
    (hA : gridIdxA n i = gridIdxA n i') (hC : gridIdxC n i = gridIdxC n i') : i = i' := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hi
    · exact h
  refine eq_of_div_mod_eq ?_ hC
  simp only [gridIdxA, gridIdxC] at hA hC
  rw [hC] at hA
  have h1 : (i' % n + i / n) % n = (i' % n + i' / n) % n := by
    rw [Nat.add_comm (i' % n) (i / n), Nat.add_comm (i' % n) (i' / n)]; exact hA
  have h2 : (i / n) % n = (i' / n) % n :=
    Nat.ModEq.add_left_cancel' (i' % n) (by simpa [Nat.ModEq] using h1)
  have hdi : i / n < n := gridIdxB_lt hi
  have hdi' : i' / n < n := gridIdxB_lt hi'
  rwa [Nat.mod_eq_of_lt hdi, Nat.mod_eq_of_lt hdi'] at h2

/-- **The `W`–`X` block pair is used at most once.** -/
theorem gridIdx_BC_inj {n i i' : ℕ}
    (hB : gridIdxB n i = gridIdxB n i') (hC : gridIdxC n i = gridIdxC n i') : i = i' :=
  eq_of_div_mod_eq hB hC

/-! ### Locating an edge in the block structure -/

/-- The two endpoints of an edge lie one in `S` and one in `T`. -/
def pairIn (S T : Finset V) (x y : V) : Prop := (x ∈ S ∧ y ∈ T) ∨ (x ∈ T ∧ y ∈ S)

omit [Fintype V] [DecidableEq V] in
theorem pairIn_symm {S T : Finset V} {x y : V} (h : pairIn S T x y) : pairIn T S x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

omit [Fintype V] [DecidableEq V] in
/-- `crossAdj` is exactly the disjunction of the three `pairIn`s. -/
theorem crossAdj_iff_pairIn {U W X : Finset V} {x y : V} :
    crossAdj U W X x y ↔ pairIn U W x y ∨ pairIn U X x y ∨ pairIn W X x y := by
  unfold crossAdj pairIn; tauto

omit [Fintype V] [DecidableEq V] in
/-- **Two different pairs of blocks cannot carry the same edge**, if one of the two blocks of the
first pair is disjoint from both blocks of the second. -/
theorem pairIn_absurd {S T S' T' : Finset V} {x y : V} (h : pairIn S T x y)
    (h' : pairIn S' T' x y) (h1 : Disjoint S S') (h2 : Disjoint S T') : False := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases h' with ⟨hx', hy'⟩ | ⟨hx', hy'⟩
  · exact (Finset.disjoint_left.mp h1 hx) hx'
  · exact (Finset.disjoint_left.mp h2 hx) hx'
  · exact (Finset.disjoint_left.mp h2 hy) hy'
  · exact (Finset.disjoint_left.mp h1 hy) hy'

omit [Fintype V] [DecidableEq V] in
/-- **The same pair of clusters carrying the same edge forces the two blocks to meet.** -/
theorem pairIn_match {S T S' T' : Finset V} {x y : V} (h : pairIn S T x y)
    (h' : pairIn S' T' x y) (hST' : Disjoint S T') (hTS' : Disjoint T S') :
    ¬ Disjoint S S' ∧ ¬ Disjoint T T' := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases h' with ⟨hx', hy'⟩ | ⟨hx', hy'⟩
  · exact ⟨fun hd => (Finset.disjoint_left.mp hd hx) hx',
      fun hd => (Finset.disjoint_left.mp hd hy) hy'⟩
  · exact absurd hx' (Finset.disjoint_left.mp hST' hx)
  · exact absurd hx' (Finset.disjoint_left.mp hTS' hx)
  · exact ⟨fun hd => (Finset.disjoint_left.mp hd hy) hy',
      fun hd => (Finset.disjoint_left.mp hd hx) hx'⟩

/-! ### The design -/

/-- The `U`-part of the `i`-th member of the diagonal design. -/
def gridA (n : ℕ) (Ub : ℕ → Finset V) (i : ℕ) : Finset V := Ub (gridIdxA n i)

/-- The `W`-part of the `i`-th member of the diagonal design. -/
def gridB (n : ℕ) (Wb : ℕ → Finset V) (i : ℕ) : Finset V := Wb (gridIdxB n i)

/-- The `X`-part of the `i`-th member of the diagonal design. -/
def gridC (n : ℕ) (Xb : ℕ → Finset V) (i : ℕ) : Finset V := Xb (gridIdxC n i)

omit [Fintype V] [DecidableEq V] in
/-- **The diagonal design is edge-disjoint.**  If the sub-blocks of each cluster are pairwise
disjoint and the sub-blocks of different clusters are disjoint, then two distinct members of the
diagonal family have no common edge: a common edge determines the pair of blocks that carries it,
hence — by `Nibble.AX1.gridShift_UW_injective` and its companions, in the form
`Nibble.AX1.gridIdx_AB_inj`, `Nibble.AX1.gridIdx_AC_inj`, `Nibble.AX1.gridIdx_BC_inj` — the
member. -/
theorem gridDesign_pairwise_edgeDisjoint (G : SimpleGraph V) {n : ℕ}
    (Ub Wb Xb : ℕ → Finset V)
    (hUU : ∀ a < n, ∀ b < n, a ≠ b → Disjoint (Ub a) (Ub b))
    (hWW : ∀ a < n, ∀ b < n, a ≠ b → Disjoint (Wb a) (Wb b))
    (hXX : ∀ a < n, ∀ b < n, a ≠ b → Disjoint (Xb a) (Xb b))
    (hUW : ∀ a < n, ∀ b < n, Disjoint (Ub a) (Wb b))
    (hUX : ∀ a < n, ∀ b < n, Disjoint (Ub a) (Xb b))
    (hWX : ∀ a < n, ∀ b < n, Disjoint (Wb a) (Xb b))
    {i : ℕ} (hi : i < n * n) {i' : ℕ} (hi' : i' < n * n) (hne : i ≠ i') (x y : V)
    (h : (tripleGraph G (gridA n Ub i) (gridB n Wb i) (gridC n Xb i)).Adj x y) :
    ¬ (tripleGraph G (gridA n Ub i') (gridB n Wb i') (gridC n Xb i')).Adj x y := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hi
    · exact hpos
  intro h'
  set a := gridIdxA n i with ha
  set b := gridIdxB n i with hb
  set c := gridIdxC n i with hc
  set a' := gridIdxA n i' with ha'
  set b' := gridIdxB n i' with hb'
  set c' := gridIdxC n i' with hc'
  have hai : a < n := gridIdxA_lt hn i
  have hbi : b < n := gridIdxB_lt hi
  have hci : c < n := gridIdxC_lt hn i
  have hai' : a' < n := gridIdxA_lt hn i'
  have hbi' : b' < n := gridIdxB_lt hi'
  have hci' : c' < n := gridIdxC_lt hn i'
  have hcross : pairIn (Ub a) (Wb b) x y ∨ pairIn (Ub a) (Xb c) x y ∨ pairIn (Wb b) (Xb c) x y :=
    crossAdj_iff_pairIn.mp h.2
  have hcross' : pairIn (Ub a') (Wb b') x y ∨ pairIn (Ub a') (Xb c') x y
      ∨ pairIn (Wb b') (Xb c') x y := crossAdj_iff_pairIn.mp h'.2
  -- index equalities out of "the two blocks meet"
  have hUeq : ∀ p q, p < n → q < n → ¬ Disjoint (Ub p) (Ub q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hUU p hp q hq hpq)
  have hWeq : ∀ p q, p < n → q < n → ¬ Disjoint (Wb p) (Wb q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hWW p hp q hq hpq)
  have hXeq : ∀ p q, p < n → q < n → ¬ Disjoint (Xb p) (Xb q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hXX p hp q hq hpq)
  refine hne ?_
  rcases hcross with hUW1 | hUX1 | hWX1
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · obtain ⟨h1, h2⟩ := pairIn_match hUW1 hUW2 (hUW a hai b' hbi')
        (Disjoint.symm (hUW a' hai' b hbi))
      exact gridIdx_AB_inj hi hi' (hUeq a a' hai hai' h1) (hWeq b b' hbi hbi' h2)
    · exact absurd (pairIn_absurd (pairIn_symm hUW1) hUX2
        (Disjoint.symm (hUW a' hai' b hbi)) (hWX b hbi c' hci')) not_false
    · exact absurd (pairIn_absurd hUW1 hWX2 (hUW a hai b' hbi') (hUX a hai c' hci')) not_false
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · exact absurd (pairIn_absurd (pairIn_symm hUX1) hUW2
        (Disjoint.symm (hUX a' hai' c hci)) (Disjoint.symm (hWX b' hbi' c hci))) not_false
    · obtain ⟨h1, h2⟩ := pairIn_match hUX1 hUX2 (hUX a hai c' hci')
        (Disjoint.symm (hUX a' hai' c hci))
      exact gridIdx_AC_inj hi hi' (hUeq a a' hai hai' h1) (hXeq c c' hci hci' h2)
    · exact absurd (pairIn_absurd hUX1 hWX2 (hUW a hai b' hbi') (hUX a hai c' hci')) not_false
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · exact absurd (pairIn_absurd (pairIn_symm hWX1) hUW2
        (Disjoint.symm (hUX a' hai' c hci)) (Disjoint.symm (hWX b' hbi' c hci))) not_false
    · exact absurd (pairIn_absurd hUX2 hWX1 (hUW a' hai' b hbi) (hUX a' hai' c hci)) not_false
    · obtain ⟨h1, h2⟩ := pairIn_match hWX1 hWX2 (hWX b hbi c' hci')
        (Disjoint.symm (hWX b' hbi' c hci))
      exact gridIdx_BC_inj (hWeq b b' hbi hbi' h1) (hXeq c c' hci hci' h2)

end Nibble.AX1
