/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Digraph.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-! # Internal helpers for Valiant's Depth Reduction Lemma

Proof machinery supporting `Valiant.depth_reduction`. The public
statement and high-level wrapper live in `Circ.Valiant`; the basic
digraph definitions used below — `IsDirectedPath`, `IsSimplePath`,
`depth`, `edgeFinset`, `deleteEdges` — live in `Circ.Digraph.Defs`.
This file defines the canonical labeling and collects the canonical
labeling argument, the edge partition by first-differing bit, the
averaging step, and the relabeling-after-removal bound.
-/

namespace Digraph

/-- The **canonical labeling** of `G`: the length — node count — of a
longest simple directed path ending at `v`. Parameterized by edge
count `n`, with the outer `+ 1` converting to node count; the
single-vertex path `![v]` always witnesses `n = 0`, so the label is
automatically at least `1`. -/
noncomputable def canonicalLabel {V : Type*} [Fintype V]
    (G : Digraph V) (v : V) : Nat :=
  have _hV : Fintype V := ‹_›
  sSup { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v } + 1

end Digraph

namespace CircuitComplexity.Valiant

open Digraph

variable {V : Type*} [Fintype V]

/-! ### Acyclicity and legal labelings -/

/-- A **legal labeling** of a digraph is a map to the naturals that is
strictly increasing along every edge. -/
def IsLegalLabeling (G : Digraph V) (ℓ : V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → ℓ u < ℓ v

omit [Fintype V] in
/-- The canonical-label set is bounded above by `Fintype.card V`: any
injective `Fin (n + 1) → V` forces `n + 1 ≤ Fintype.card V`. -/
private lemma canonicalLabel_set_bddAbove [Finite V] (G : Digraph V) (v : V) :
    BddAbove { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v } := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨p, ⟨_, hinj⟩, _⟩
  have := Fintype.card_le_of_injective p hinj
  simp only [Fintype.card_fin] at this
  omega

omit [Fintype V] in
/-- The single-vertex path at `v` witnesses `0` in the canonical-label
edge-count set. -/
private lemma zero_mem_canonicalLabel_set (G : Digraph V) (v : V) :
    (0 : ℕ) ∈ { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v } := by
  refine ⟨fun _ => v, ⟨fun i h => by omega, ?_⟩, rfl⟩
  intro a b _
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- Every canonical label is at least `1`: immediate from the outer
`+ 1` in the definition. -/
lemma one_le_canonicalLabel (G : Digraph V) (v : V) :
    1 ≤ G.canonicalLabel v := by
  change 1 ≤ _ + 1
  omega

/-- In an acyclic digraph, the canonical label is bounded above by the
graph's depth. (In a cyclic digraph the canonical label can exceed the
walk-supremum `depth = 0`, so acyclicity is needed.) -/
lemma canonicalLabel_le_depth
    (G : Digraph V) (hac : IsAcyclic G) (v : V) :
    G.canonicalLabel v ≤ G.depth := by
  set S : Set ℕ := { n | ∃ p : Fin (n + 1) → V, G.IsSimplePath p ∧ p (Fin.last n) = v }
  change sSup S + 1 ≤ G.depth
  obtain ⟨p, ⟨hpath, _⟩, _⟩ :=
    Nat.sSup_mem ⟨0, zero_mem_canonicalLabel_set G v⟩ (canonicalLabel_set_bddAbove G v)
  exact le_csSup hac ⟨p, hpath⟩

/-- Under `G.depth ≤ 2 ^ k` (with `G` acyclic), every canonical label
lies in `{1,...,2^k}`, so `ℓ(v) - 1 < 2 ^ k`. -/
private lemma canonicalLabel_sub_one_lt_two_pow
    (G : Digraph V) (hac : IsAcyclic G) {k : ℕ} (hd : G.depth ≤ 2 ^ k)
    (v : V) : G.canonicalLabel v - 1 < 2 ^ k := by
  have h1 : G.canonicalLabel v ≤ 2 ^ k := (canonicalLabel_le_depth G hac v).trans hd
  have h2 : 1 ≤ G.canonicalLabel v := one_le_canonicalLabel G v
  omega

omit [Fintype V] in
/-- **Cycle contradiction.** A simple path `p` of length `m` ending at `u`,
together with an edge `u → v` and an occurrence of `v` within `p`, closes
a cycle. We can then build directed walks of arbitrary length by repeatedly
going around the cycle, so `G` is not acyclic. -/
private lemma not_acyclic_of_cycle_witness
    (G : Digraph V) {u v : V} (huv : G.Adj u v)
    {m : ℕ} (p : Fin m → V) (hpath : G.IsDirectedPath p)
    (iu iv : Fin m) (hpu : p iu = u) (hiu : iu.val + 1 = m) (hpv : p iv = v) :
    ¬ IsAcyclic G := by
  rw [IsAcyclic, not_bddAbove_iff]
  intro N
  have hiv_lt_m : iv.val < m := iv.isLt
  have hL_pos : 0 < m - iv.val := by omega
  have h_bnd : ∀ j : ℕ, iv.val + j % (m - iv.val) < m := fun j => by
    have := Nat.mod_lt j hL_pos; omega
  refine ⟨N + 1,
    ⟨fun k : Fin (N + 1) => p ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩, ?_⟩,
    Nat.lt_succ_self _⟩
  intro k hk
  have h_a_lt : k.val % (m - iv.val) < m - iv.val := Nat.mod_lt _ hL_pos
  have h_add_mod : (k.val + 1) % (m - iv.val) =
      (k.val % (m - iv.val) + 1) % (m - iv.val) := by
    have hdm := Nat.div_add_mod k.val (m - iv.val)
    have heq : k.val + 1 =
        (k.val % (m - iv.val) + 1) + (m - iv.val) * (k.val / (m - iv.val)) := by
      omega
    rw [heq, Nat.add_mul_mod_self_left]
  by_cases hwrap : k.val % (m - iv.val) + 1 = m - iv.val
  · have h_next : (k.val + 1) % (m - iv.val) = 0 := by
      rw [h_add_mod, hwrap, Nat.mod_self]
    have h_a_eq : k.val % (m - iv.val) = m - iv.val - 1 := by omega
    have hu_eq : p ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩ = u := by
      have hval : iv.val + k.val % (m - iv.val) = iu.val := by omega
      rw [show (⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩ : Fin m) = iu from
        Fin.ext hval, hpu]
    have hv_eq : p ⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩ = v := by
      have : (⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩ : Fin m) = iv := by
        apply Fin.ext
        change iv.val + (k.val + 1) % (m - iv.val) = iv.val
        rw [h_next]; rfl
      rw [this, hpv]
    change G.Adj (p ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩)
               (p ⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩)
    rw [hu_eq, hv_eq]
    exact huv
  · have hlt : k.val % (m - iv.val) + 1 < m - iv.val := by omega
    have h_next : (k.val + 1) % (m - iv.val) = k.val % (m - iv.val) + 1 := by
      rw [h_add_mod, Nat.mod_eq_of_lt hlt]
    have hbnd2 : iv.val + k.val % (m - iv.val) + 1 < m := by omega
    have step := hpath ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩ hbnd2
    have h_target :
        (⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩ : Fin m) =
        ⟨iv.val + k.val % (m - iv.val) + 1, hbnd2⟩ := by
      apply Fin.ext
      change iv.val + (k.val + 1) % (m - iv.val) = iv.val + k.val % (m - iv.val) + 1
      omega
    change G.Adj (p ⟨iv.val + k.val % (m - iv.val), h_bnd k.val⟩)
               (p ⟨iv.val + (k.val + 1) % (m - iv.val), h_bnd (k.val + 1)⟩)
    rw [h_target]
    exact step

omit [Fintype V] in
/-- **Extending a simple path by an edge.** In an acyclic digraph, a
simple path `p` ending at `u` followed by an edge `u → v` yields a
simple path ending at `v` that is one longer. -/
private lemma extend_simple_path (G : Digraph V) (hac : IsAcyclic G)
    {u v : V} (huv : G.Adj u v) {n : ℕ} {p : Fin (n + 1) → V}
    (hsp : G.IsSimplePath p) (hpu : p (Fin.last n) = u) :
    ∃ p' : Fin (n + 2) → V, G.IsSimplePath p' ∧ p' (Fin.last (n + 1)) = v := by
  classical
  obtain ⟨hpath, hinj⟩ := hsp
  have hv_notin : ∀ i : Fin (n + 1), p i ≠ v := fun i hpv =>
    not_acyclic_of_cycle_witness G huv p hpath (Fin.last n) i hpu rfl hpv hac
  refine ⟨fun k => if h : k.val < n + 1 then p ⟨k.val, h⟩ else v, ⟨?_, ?_⟩, ?_⟩
  · intro k hk
    dsimp only
    split_ifs with h₁ h₂
    · exact hpath ⟨k.val, h₁⟩ h₂
    · have heq : (⟨k.val, h₁⟩ : Fin (n + 1)) = Fin.last n := by
        apply Fin.ext; change k.val = n; omega
      rw [heq, hpu]; exact huv
    · omega
    · omega
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    dsimp only at hab
    split_ifs at hab with h₁ h₂ h₃
    · apply Fin.ext; exact Fin.mk_eq_mk.mp (hinj hab)
    · exact absurd hab (hv_notin ⟨a, h₁⟩)
    · exact absurd hab.symm (hv_notin ⟨b, h₃⟩)
    · apply Fin.ext; change a = b; omega
  · change (if h : (Fin.last (n + 1)).val < n + 1 then _ else v) = v
    simp [Fin.last]

/-- **Canonical labeling is legal in acyclic graphs.** Any simple path
ending at `u` followed by the edge `(u,v)` is a strictly longer simple
path ending at `v` (using acyclicity to ensure `v` does not already
appear in the path). -/
lemma canonicalLabel_isLegal (G : Digraph V) (hac : IsAcyclic G) :
    IsLegalLabeling G G.canonicalLabel := by
  classical
  intro u v huv
  obtain ⟨p, hsp, hpu⟩ :=
    Nat.sSup_mem ⟨0, zero_mem_canonicalLabel_set G u⟩ (canonicalLabel_set_bddAbove G u)
  obtain ⟨p', hsp', hend⟩ := extend_simple_path G hac huv hsp hpu
  have hle := le_csSup (canonicalLabel_set_bddAbove G v) ⟨p', hsp', hend⟩
  change _ + 1 < _ + 1
  omega

section LegalLabelHelpers

variable {V : Type*}

/-- Under a legal labeling, the label increases by at least the index
gap along any directed walk. -/
private lemma legal_label_add_le
    {G : Digraph V} {ℓ : V → ℕ} (hℓ : IsLegalLabeling G ℓ)
    {m : ℕ} {p : Fin m → V} (hp : G.IsDirectedPath p) :
    ∀ k a (h₁ : a < m) (h₂ : a + k < m),
      ℓ (p ⟨a, h₁⟩) + k ≤ ℓ (p ⟨a + k, h₂⟩) := by
  intro k
  induction k with
  | zero =>
    intro a _ _
    rfl
  | succ k ih =>
    intro a h₁ h₂
    have hak : a + k < m := by omega
    have ihk := ih a h₁ hak
    have step : G.Adj (p ⟨a + k, hak⟩) (p ⟨a + k + 1, h₂⟩) :=
      hp ⟨a + k, hak⟩ h₂
    have stepl : ℓ (p ⟨a + k, hak⟩) < ℓ (p ⟨a + k + 1, h₂⟩) :=
      hℓ _ _ step
    change ℓ (p ⟨a, h₁⟩) + (k + 1) ≤ ℓ (p ⟨a + k + 1, h₂⟩)
    omega

/-- The label sequence along a directed walk under a legal labeling
is strictly monotonic. -/
private lemma legal_label_strictMono
    {G : Digraph V} {ℓ : V → ℕ} (hℓ : IsLegalLabeling G ℓ)
    {m : ℕ} {p : Fin m → V} (hp : G.IsDirectedPath p) :
    StrictMono (fun i : Fin m => ℓ (p i)) := by
  intro i j hij
  have hile : i.val < j.val := hij
  have hd : i.val + (j.val - i.val) < m := by
    have : i.val + (j.val - i.val) = j.val := by omega
    rw [this]; exact j.isLt
  have key := legal_label_add_le hℓ hp (j.val - i.val) i.val i.isLt hd
  have e1 : (⟨i.val, i.isLt⟩ : Fin m) = i := rfl
  have e2 : (⟨i.val + (j.val - i.val), hd⟩ : Fin m) = j := by
    apply Fin.ext
    change i.val + (j.val - i.val) = j.val
    omega
  rw [e1, e2] at key
  change ℓ (p i) < ℓ (p j)
  have : 0 < j.val - i.val := by omega
  omega

end LegalLabelHelpers

/-- **Depth bound from a legal labeling.** Along any directed path,
labels are strictly increasing, hence distinct. So `depth(G)` is at
most the number of distinct labels used by any legal labeling. -/
lemma depth_le_image_card (G : Digraph V)
    {ℓ : V → ℕ} (hℓ : IsLegalLabeling G ℓ) :
    G.depth ≤ (Finset.univ.image ℓ).card := by
  unfold Digraph.depth
  apply csSup_le
  · exact ⟨0, fun (i : Fin 0) => i.elim0, fun i _ => i.elim0⟩
  · rintro m ⟨p, hp⟩
    have hinj : Function.Injective (fun i : Fin m => ℓ (p i)) :=
      (legal_label_strictMono hℓ hp).injective
    have hsubset :
        (Finset.univ : Finset (Fin m)).image (fun i => ℓ (p i)) ⊆
          Finset.univ.image ℓ := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, hi⟩ := hx
      exact ⟨p i, hi⟩
    have hcard :
        ((Finset.univ : Finset (Fin m)).image (fun i => ℓ (p i))).card = m := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    calc m = ((Finset.univ : Finset (Fin m)).image (fun i => ℓ (p i))).card := hcard.symm
      _ ≤ (Finset.univ.image ℓ).card := Finset.card_le_card hsubset

/-! ### Partitioning edges by first-differing bit

Under `IsAcyclic G` and `G.depth ≤ 2 ^ k`, each canonical label
`G.canonicalLabel v` lies in `{1,...,2^k}`, so after subtracting 1
its `k`-bit binary representation is well-defined. For each edge
`(u,v)`, since canonical labels are strictly increasing, the `k`-bit
reps of `ℓ(u)-1` and `ℓ(v)-1` differ, and we can identify the
leftmost (MSB) bit at which they first disagree. -/

/-- At positions where `x ^^^ y` has bit `false`, the bits of `x` and `y` agree. -/
private lemma testBit_eq_of_xor_testBit_false
    {x y m : ℕ} (hxor_m : (x ^^^ y).testBit m = false) :
    x.testBit m = y.testBit m := by
  rw [Nat.testBit_xor] at hxor_m
  cases hxb : x.testBit m <;> cases hyb : y.testBit m <;>
    simp [hxb, hyb] at hxor_m <;> rfl

/-- `firstDifferBit k a b` is the 1-indexed MSB position at which the
`k`-bit binary representations of `a` and `b` first disagree, or `0`
if the two `k`-bit representations coincide. The MSB of `a XOR b` (as
indexed by `Nat.log2` from the LSB) gives the position of first
difference; converting to 1-indexed-from-MSB gives `k - Nat.log2`. -/
def firstDifferBit (k a b : ℕ) : ℕ :=
  if a = b then 0 else k - Nat.log2 (a ^^^ b)

omit [Fintype V] in
/-- For `x ≠ y` both below `2 ^ k`, `firstDifferBit k x y` lies in
`{1,...,k}` and `k - firstDifferBit k x y = Nat.log2 (x ^^^ y)`. -/
private lemma firstDifferBit_of_ne
    {k x y : ℕ} (hxne : x ≠ y) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    1 ≤ firstDifferBit k x y ∧
    firstDifferBit k x y ≤ k ∧
    k - firstDifferBit k x y = Nat.log2 (x ^^^ y) := by
  have hxor_ne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr hxne
  have hxor_lt : x ^^^ y < 2 ^ k := Nat.xor_lt_two_pow hx hy
  have hlog_lt : Nat.log2 (x ^^^ y) < k := (Nat.log2_lt hxor_ne).mpr hxor_lt
  simp only [firstDifferBit, if_neg hxne]
  omega

omit [Fintype V] in
/-- Above the pivot `k - firstDifferBit k x y`, bits of `x` and `y` agree. -/
private lemma testBit_eq_above_firstDifferBit
    {k x y : ℕ} (hxne : x ≠ y) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    {m : ℕ} (hm : k - firstDifferBit k x y < m) :
    x.testBit m = y.testBit m := by
  have hxor_ne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr hxne
  obtain ⟨_, _, hkj_eq⟩ := firstDifferBit_of_ne hxne hx hy
  rw [hkj_eq] at hm
  exact testBit_eq_of_xor_testBit_false
    (Nat.testBit_lt_two_pow ((Nat.log2_lt hxor_ne).mp hm))

omit [Fintype V] in
/-- At the pivot position, if `x < y` then `x`'s bit is `false` and `y`'s
is `true`: `x` must have the 0 and `y` the 1 for the strict inequality. -/
private lemma testBit_firstDifferBit_pivot_of_lt
    {k x y : ℕ} (hxy : x < y) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x.testBit (k - firstDifferBit k x y) = false ∧
    y.testBit (k - firstDifferBit k x y) = true := by
  set j := firstDifferBit k x y
  have hxne : x ≠ y := hxy.ne
  have hxor_ne : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr hxne
  obtain ⟨_, _, hkj_eq⟩ := firstDifferBit_of_ne hxne hx hy
  have hxor_bit : (x ^^^ y).testBit (k - j) = true := by
    rw [hkj_eq]; exact Nat.testBit_log2 hxor_ne
  have hagree : ∀ m, k - j < m → x.testBit m = y.testBit m :=
    fun m hm => testBit_eq_above_firstDifferBit hxne hx hy hm
  rw [Nat.testBit_xor] at hxor_bit
  cases hxb : x.testBit (k - j) <;> cases hyb : y.testBit (k - j)
  · simp [hxb, hyb] at hxor_bit
  · exact ⟨rfl, rfl⟩
  · exfalso
    have : y < x := Nat.lt_of_testBit (k - j) hyb hxb
      (fun m hm => (hagree m hm).symm)
    omega
  · simp [hxb, hyb] at hxor_bit

variable [DecidableEq V]

/-- Edges whose canonical-label endpoints' `k`-bit binary
representations first disagree at MSB position `i`. -/
noncomputable def levelEdges
    (G : Digraph V) [DecidableRel G.Adj] (k i : ℕ) : Finset (V × V) :=
  G.edgeFinset.filter (fun e =>
    firstDifferBit k (G.canonicalLabel e.1 - 1) (G.canonicalLabel e.2 - 1) = i)

/-- For any edge `(u,v)` of an acyclic `G` with `depth ≤ 2 ^ k`, the first
MSB-disagreement of the `k`-bit canonical labels is in `{1,...,k}`. -/
private lemma firstDifferBit_mem_Ioc
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k)
    {e : V × V} (he : e ∈ G.edgeFinset) :
    firstDifferBit k (G.canonicalLabel e.1 - 1) (G.canonicalLabel e.2 - 1) ∈
      Finset.Ioc 0 k := by
  have huv : G.Adj e.1 e.2 := Digraph.mem_edgeFinset.mp he
  have h12 : G.canonicalLabel e.1 < G.canonicalLabel e.2 :=
    canonicalLabel_isLegal G hac _ _ huv
  have h1' : 1 ≤ G.canonicalLabel e.1 := one_le_canonicalLabel G _
  have hab : G.canonicalLabel e.1 - 1 ≠ G.canonicalLabel e.2 - 1 := by omega
  obtain ⟨hpos, hle, _⟩ := firstDifferBit_of_ne hab
    (canonicalLabel_sub_one_lt_two_pow G hac hd _)
    (canonicalLabel_sub_one_lt_two_pow G hac hd _)
  exact Finset.mem_Ioc.mpr ⟨hpos, hle⟩

/-- **Partition.** When `G` is acyclic and `G.depth ≤ 2 ^ k`, every
edge lies in exactly one level `E_i` for `i ∈ {1,...,k}`. -/
lemma sum_card_levelEdges_eq
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k) :
    ∑ i ∈ Finset.Ioc 0 k, (levelEdges G k i).card = G.edgeFinset.card := by
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun e he => firstDifferBit_mem_Ioc G hac hd he)

/-- **Averaging helper.** If `s` has `n` elements, then for any `r ≤ n`
there is an `r`-subset `I ⊆ s` with `n * (∑ I, a) ≤ r * (∑ s, a)`. Proved
by repeatedly peeling off the element with the largest `a`-value. -/
private lemma exists_r_subset_sum_le
    {α : Type*} (a : α → ℕ) :
    ∀ (n : ℕ) (s : Finset α), s.card = n → ∀ (r : ℕ), r ≤ n →
      ∃ I ⊆ s, I.card = r ∧ n * (∑ i ∈ I, a i) ≤ r * (∑ i ∈ s, a i) := by
  classical
  intro n
  induction n with
  | zero =>
    intro s hs r hr
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    have : s = ∅ := Finset.card_eq_zero.mp hs
    subst this
    exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ n' ih =>
    intro s hs r hr
    by_cases hr_eq : r = n' + 1
    · subst hr_eq
      exact ⟨s, Finset.Subset.refl _, hs, le_refl _⟩
    · have hr_lt : r ≤ n' := by omega
      have hs_ne : s.Nonempty := Finset.card_pos.mp (by rw [hs]; omega)
      obtain ⟨jmax, hjmax_mem, hjmax_max⟩ := s.exists_max_image a hs_ne
      let s' := s.erase jmax
      have hs'_card : s'.card = n' := by
        simp [s', Finset.card_erase_of_mem hjmax_mem, hs]
      obtain ⟨I, hI_sub, hI_card, hI_le⟩ := ih s' hs'_card r hr_lt
      refine ⟨I, hI_sub.trans (Finset.erase_subset _ _), hI_card, ?_⟩
      have hsum_s : ∑ i ∈ s, a i = ∑ i ∈ s', a i + a jmax :=
        (Finset.sum_erase_add _ _ hjmax_mem).symm
      have hsumI_le : ∑ i ∈ I, a i ≤ I.card * a jmax := by
        have hbound : ∀ i ∈ I, a i ≤ a jmax := fun i hi =>
          hjmax_max i (hI_sub.trans (Finset.erase_subset _ _) hi)
        exact Finset.sum_le_card_nsmul I a (a jmax) hbound
      rw [hI_card] at hsumI_le
      rw [hsum_s]
      have h_lhs_expand :
          (n' + 1) * (∑ i ∈ I, a i) =
            n' * (∑ i ∈ I, a i) + (∑ i ∈ I, a i) := by ring
      have h_rhs_expand :
          r * (∑ i ∈ s', a i + a jmax) = r * (∑ i ∈ s', a i) + r * a jmax := by ring
      rw [h_lhs_expand, h_rhs_expand]
      have hih_step : n' * (∑ i ∈ I, a i) ≤ r * (∑ i ∈ s', a i) := hI_le
      omega

/-- **Averaging.** There is a choice of `r` levels whose total edge
count is at most `r * S / k` (equivalently, `k * total ≤ r * S`). -/
lemma exists_r_levels_small
    (G : Digraph V) [DecidableRel G.Adj] {k r : ℕ} (hrk : r ≤ k)
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k) :
    ∃ I : Finset ℕ, I ⊆ Finset.Ioc 0 k ∧ I.card = r ∧
      k * (∑ i ∈ I, (levelEdges G k i).card) ≤ r * G.edgeFinset.card := by
  have hsum : ∑ i ∈ Finset.Ioc 0 k, (levelEdges G k i).card = G.edgeFinset.card :=
    sum_card_levelEdges_eq G hac hd
  have hcard : (Finset.Ioc 0 k).card = k := by simp
  obtain ⟨I, hI_sub, hI_card, hI_le⟩ :=
    exists_r_subset_sum_le (fun i => (levelEdges G k i).card)
      k (Finset.Ioc 0 k) hcard r hrk
  refine ⟨I, hI_sub, hI_card, ?_⟩
  rw [hsum] at hI_le
  exact hI_le

/-- Restrict `x` to its `k` low bits, then zero out the bits at MSB
positions `i ∈ I` (1-indexed; equivalently, LSB positions `k - i`). -/
private def maskOutI (k : ℕ) (I : Finset ℕ) (x : ℕ) : ℕ :=
  ∑ i ∈ (Finset.Ioc 0 k) \ I,
    (if x.testBit (k - i) then 2 ^ (k - i) else 0)

omit [Fintype V] [DecidableEq V] in
/-- Geometric series: `∑ m ∈ range n, 2^m = 2^n - 1`. -/
private lemma sum_range_pow_two (n : ℕ) :
    ∑ m ∈ Finset.range n, (2 : ℕ) ^ m = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    omega

omit [Fintype V] [DecidableEq V] in
/-- **Split the mask sum at a pivot.** For `j ∈ (Ioc 0 k) \ I`, the
`maskOutI` sum decomposes into contributions above `j`, at `j`, and below. -/
private lemma maskOutI_split_at_pivot
    {k : ℕ} {I : Finset ℕ} {j : ℕ}
    (hj : j ∈ (Finset.Ioc 0 k) \ I) (z : ℕ) :
    maskOutI k I z =
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (· < j),
        if z.testBit (k - i) then 2 ^ (k - i) else 0) +
      (if z.testBit (k - j) then 2 ^ (k - j) else 0) +
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (j < ·),
        if z.testBit (k - i) then 2 ^ (k - i) else 0) := by
  set D : Finset ℕ := (Finset.Ioc 0 k) \ I
  have hmask : maskOutI k I z =
      (if z.testBit (k - j) then 2 ^ (k - j) else 0) +
      ∑ i ∈ D.erase j, (if z.testBit (k - i) then 2 ^ (k - i) else 0) := by
    change (∑ i ∈ D, if z.testBit (k - i) then 2 ^ (k - i) else 0) = _
    conv_lhs => rw [(Finset.insert_erase hj).symm]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  have h_filt_lt : (D.erase j).filter (· < j) = D.filter (· < j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase]
    refine ⟨fun ⟨⟨_, hD⟩, hlt⟩ => ⟨hD, hlt⟩, fun ⟨hD, hlt⟩ => ⟨⟨?_, hD⟩, hlt⟩⟩
    omega
  have h_filt_gt : (D.erase j).filter (fun i => ¬ i < j) = D.filter (j < ·) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase]
    refine ⟨fun ⟨⟨_, hD⟩, hnlt⟩ => ⟨hD, ?_⟩, fun ⟨hD, hgt⟩ => ⟨⟨?_, hD⟩, ?_⟩⟩ <;> omega
  rw [hmask, ← (Finset.sum_filter_add_sum_filter_not (D.erase j) (· < j) _),
      h_filt_lt, h_filt_gt]
  ring

omit [Fintype V] [DecidableEq V] in
/-- **Below-pivot bound.** The sum of mask contributions at positions below
the pivot `j` is strictly less than `2 ^ (k - j)` (geometric-series bound). -/
private lemma maskOutI_sum_below_lt
    {k : ℕ} (I : Finset ℕ) {j : ℕ} (hj_le : j ≤ k) (z : ℕ) :
    (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (j < ·),
      if z.testBit (k - i) then 2 ^ (k - i) else 0) < 2 ^ (k - j) := by
  have h1 :
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (j < ·),
        if z.testBit (k - i) then 2 ^ (k - i) else 0) ≤
      ∑ i ∈ Finset.Ioc j k, 2 ^ (k - i) := by
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun _ _ _ => Nat.zero_le _))
    · split_ifs
      · rfl
      · exact Nat.zero_le _
    · simp only [Finset.mem_filter, Finset.mem_Ioc] at hi ⊢
      exact ⟨hi.2, (Finset.mem_Ioc.mp (Finset.mem_sdiff.mp hi.1).1).2⟩
  have h2 : (∑ i ∈ Finset.Ioc j k, (2 : ℕ) ^ (k - i)) = 2 ^ (k - j) - 1 := by
    rw [show (∑ i ∈ Finset.Ioc j k, (2:ℕ) ^ (k - i)) =
            ∑ m ∈ Finset.range (k - j), (2:ℕ) ^ m from ?_, sum_range_pow_two]
    apply Finset.sum_nbij (fun i => k - i)
    · intro i hi; simp only [Finset.mem_Ioc, Finset.mem_range] at hi ⊢; omega
    · intro a ha b hb hab
      simp only [Finset.coe_Ioc, Set.mem_Ioc] at ha hb
      dsimp at hab; omega
    · intro m hm
      simp only [Finset.coe_range, Set.mem_Iio] at hm
      exact ⟨k - m, by simp only [Finset.coe_Ioc, Set.mem_Ioc]; omega, by dsimp; omega⟩
    · intros; rfl
  have h3 : 0 < 2 ^ (k - j) := Nat.two_pow_pos _
  omega

omit [Fintype V] [DecidableEq V] in
/-- **Key legality.** If `x < y < 2 ^ k` and their first MSB disagreement
is *not* in `I`, then `maskOutI k I x < maskOutI k I y`.

**Proof.** Let `j = firstDifferBit k x y ∈ {1,...,k}`. Split `maskOutI`
at the pivot `j`: upper terms (`i < j`) agree between `x` and `y`; the
pivot term contributes `0` for `x` and `2^(k-j)` for `y`; the lower sum
is bounded by `2^(k-j) - 1`. So `mask(y) - mask(x) ≥ 1`. -/
private lemma maskOutI_lt_of_firstDifferBit_not_mem
    {k : ℕ} {I : Finset ℕ}
    {x y : ℕ} (hxy : x < y) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (hfd : firstDifferBit k x y ∉ I) :
    maskOutI k I x < maskOutI k I y := by
  obtain ⟨hj_pos, hj_le, _⟩ := firstDifferBit_of_ne hxy.ne hx hy
  obtain ⟨hx_bit_false, hy_bit_true⟩ := testBit_firstDifferBit_pivot_of_lt hxy hx hy
  set j := firstDifferBit k x y
  have hj_mem_D : j ∈ (Finset.Ioc 0 k) \ I :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_Ioc.mpr ⟨hj_pos, hj_le⟩, hfd⟩
  have hup_eq :
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (· < j),
        if x.testBit (k - i) then 2 ^ (k - i) else 0) =
      (∑ i ∈ ((Finset.Ioc 0 k) \ I).filter (· < j),
        if y.testBit (k - i) then 2 ^ (k - i) else 0) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_lt : i < j := (Finset.mem_filter.mp hi).2
    have hi_le_k : i ≤ k :=
      (Finset.mem_Ioc.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).1).2
    rw [testBit_eq_above_firstDifferBit hxy.ne hx hy (by omega : k - j < k - i)]
  have hmask_x := maskOutI_split_at_pivot hj_mem_D x
  have hmask_y := maskOutI_split_at_pivot hj_mem_D y
  rw [hx_bit_false] at hmask_x
  rw [hy_bit_true] at hmask_y
  simp only [Bool.false_eq_true, if_false, add_zero, if_true] at hmask_x hmask_y
  have hlow_x_lt := maskOutI_sum_below_lt I hj_le x
  rw [hmask_x, hmask_y, ← hup_eq]
  omega

omit [DecidableEq V] in
/-- **Image bound.** The image of `maskOutI k I` over any function `f : V → ℕ`
has at most `2 ^ (k - |I|)` elements, because `maskOutI k I x` is determined
by the `k - |I|` bits of `x` at positions outside `I`. -/
private lemma maskOutI_image_card_le
    {k : ℕ} {I : Finset ℕ} (hI : I ⊆ Finset.Ioc 0 k)
    (f : V → ℕ) :
    (Finset.univ.image (fun v => maskOutI k I (f v))).card ≤ 2 ^ (k - I.card) := by
  let D : Finset ℕ := (Finset.Ioc 0 k) \ I
  have hD_card : D.card = k - I.card := by
    change ((Finset.Ioc 0 k) \ I).card = k - I.card
    rw [Finset.card_sdiff_of_subset hI]
    simp
  let gbar : V → ({i // i ∈ D} → Bool) := fun v i => (f v).testBit (k - i.val)
  let φ : ({i // i ∈ D} → Bool) → ℕ := fun b =>
    ∑ i ∈ D.attach, if b i then 2 ^ (k - i.val) else 0
  have heq : ∀ v, maskOutI k I (f v) = φ (gbar v) := by
    intro v
    change (∑ i ∈ (Finset.Ioc 0 k) \ I,
            if (f v).testBit (k - i) then 2 ^ (k - i) else 0) =
         (∑ i ∈ D.attach,
            if (gbar v) i then 2 ^ (k - i.val) else 0)
    exact (Finset.sum_attach D
      (fun i => if (f v).testBit (k - i) then 2 ^ (k - i) else 0)).symm
  calc (Finset.univ.image (fun v => maskOutI k I (f v))).card
      = (Finset.univ.image (fun v => φ (gbar v))).card := by
          apply congrArg Finset.card
          exact Finset.image_congr (fun v _ => heq v)
    _ = ((Finset.univ.image gbar).image φ).card := by
          rw [show (fun v => φ (gbar v)) = φ ∘ gbar from rfl, ← Finset.image_image]
    _ ≤ (Finset.univ.image gbar).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset ({i // i ∈ D} → Bool)).card :=
          Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card ({i // i ∈ D} → Bool) := Finset.card_univ
    _ = 2 ^ D.card := by
          rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ = 2 ^ (k - I.card) := by rw [hD_card]

/-- **Relabeling after removal.** After removing the edges in levels
`I` (assuming `G` acyclic), the map sending each vertex to its
canonical label with the `I`-th bits deleted is a legal labeling of
the remaining graph; its image has at most `2 ^ (k - I.card)` values,
so the remaining depth is bounded by that. -/
lemma depth_deleteEdges_levelEdges_le
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ioc 0 k) :
    (G.deleteEdges (I.biUnion fun i => levelEdges G k i)).depth
      ≤ 2 ^ (k - I.card) := by
  set G' := G.deleteEdges (I.biUnion fun i => levelEdges G k i)
  let ℓ : V → ℕ := fun v => maskOutI k I (G.canonicalLabel v - 1)
  have hlegal : IsLegalLabeling G' ℓ := by
    intro u v huv
    have huv_G : G.Adj u v := huv.1
    have huv_not_I : (u, v) ∉ I.biUnion fun i => levelEdges G k i := huv.2
    have hedge : (u, v) ∈ G.edgeFinset := Digraph.mem_edgeFinset.mpr huv_G
    have hfd_not_in_I :
        firstDifferBit k (G.canonicalLabel u - 1) (G.canonicalLabel v - 1) ∉ I := by
      intro h
      apply huv_not_I
      rw [Finset.mem_biUnion]
      exact ⟨_, h, Finset.mem_filter.mpr ⟨hedge, rfl⟩⟩
    have hcanon_lt : G.canonicalLabel u < G.canonicalLabel v :=
      canonicalLabel_isLegal G hac _ _ huv_G
    have hcu_pos : 1 ≤ G.canonicalLabel u := one_le_canonicalLabel G _
    have hu_lt : G.canonicalLabel u - 1 < 2 ^ k :=
      canonicalLabel_sub_one_lt_two_pow G hac hd _
    have hv_lt : G.canonicalLabel v - 1 < 2 ^ k :=
      canonicalLabel_sub_one_lt_two_pow G hac hd _
    have hxy : G.canonicalLabel u - 1 < G.canonicalLabel v - 1 := by omega
    exact maskOutI_lt_of_firstDifferBit_not_mem hxy hu_lt hv_lt hfd_not_in_I
  have himg : (Finset.univ.image ℓ).card ≤ 2 ^ (k - I.card) :=
    maskOutI_image_card_le hI _
  exact (depth_le_image_card G' hlegal).trans himg

end CircuitComplexity.Valiant
