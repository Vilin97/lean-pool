/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Search

/-!
# Harvested automorphisms, and how they act on the search tree

When two leaves of the search tree carry the same certificate, the algorithm records the
permutation `autoOf` that carries one labelling to the other and uses it to prune: any child of
the current node that is in the orbit of an already-processed child can be skipped.

This file proves the two facts that pruning rests on:

* `autoOf_isAuto` — the recorded permutation really is an automorphism;
* `reach_child_auto` — an automorphism fixing the current partition carries the subtree below one
  child bijectively onto the subtree below its image, *with the same leaf keys*, so skipping the
  image loses nothing.

The bridge between the two is `ofOracle_congr`: an automorphism `γ` of `G` satisfies
`Graph.ofOracle n (f ∘ γ) = Graph.ofOracle n f`, which turns every equivariance lemma of
`IsoGraph.Canon.Equivariance` into a statement about the action of `Aut G` on the tree.
-/


namespace IsoGraph
namespace Canon


/-! ### `autoOf` really produces an automorphism -/

/-- A `PermArr n a` is an array that represents a permutation of `{0, …, n-1}`: the shape the
labelling of a leaf always has (`LeafOk`). -/
structure PermArr (n : Nat) (a : Array Nat) : Prop where
  /-- It has the right length. -/
  size : a.size = n
  /-- Its entries are vertices. -/
  lt : ∀ i, i < n → a[i]! < n
  /-- Its entries are distinct. -/
  inj : ∀ i, i < n → ∀ j, j < n → a[i]! = a[j]! → i = j

/-- The function view of a permutation array. -/
theorem PermArr.isPerm {n : Nat} {a : Array Nat} (h : PermArr n a) :
    IsPerm n (fun i => a[i]!) :=
  ⟨h.lt, h.inj⟩

theorem PermArr.surj {n : Nat} {a : Array Nat} (h : PermArr n a) {w : Nat} (hw : w < n) :
    ∃ i, i < n ∧ a[i]! = w :=
  h.isPerm.surj hw

theorem autoOf_foldl_size (σ τ : Array Nat) (l : List Nat) (b : Array Nat) :
    (l.foldl (fun g i => g.set! σ[i]! τ[i]!) b).size = b.size := by
  induction l generalizing b with
  | nil => rfl
  | cons c t ih => rw [List.foldl_cons, ih]; simp

theorem autoOf_foldl_unchanged (σ τ : Array Nat) (l : List Nat) (b : Array Nat) (x : Nat)
    (h : ∀ i ∈ l, σ[i]! ≠ x) :
    (l.foldl (fun g i => g.set! σ[i]! τ[i]!) b)[x]! = b[x]! := by
  induction l generalizing b with
  | nil => rfl
  | cons c t ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact getElemD_setD_ne (Ne.symm (h c (by simp)))

theorem autoOf_foldl_get (n : Nat) (σ τ : Array Nat) (l : List Nat) (hnd : l.Nodup)
    (hinj : ∀ i ∈ l, ∀ j ∈ l, σ[i]! = σ[j]! → i = j) (b : Array Nat) (hb : b.size = n)
    (i : Nat) (hi : i ∈ l) (hσi : σ[i]! < n) :
    (l.foldl (fun g i => g.set! σ[i]! τ[i]!) b)[σ[i]!]! = τ[i]! := by
  induction l generalizing b with
  | nil => cases hi
  | cons c t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hit
    · have hne : ∀ j ∈ t, σ[j]! ≠ σ[i]! := by
        intro j hj heq
        exact absurd (hinj j (List.mem_cons_of_mem _ hj) i (by simp) heq ▸ hj)
          (List.nodup_cons.1 hnd).1
      rw [autoOf_foldl_unchanged σ τ t _ _ hne,
        getElemD_setD (show σ[i]! < b.size by rw [hb]; exact hσi) σ[i]!, ite_eq_left rfl]
    · exact ih (List.nodup_cons.1 hnd).2
        (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) _
        (by simp [hb]) hit

/-- Reading `autoOf` back: it sends the vertex at position `i` of `σ` to the one at position `i`
of `τ`. -/
theorem autoOf_get {n : Nat} {σ τ : Array Nat} (hσ : PermArr n σ) {i : Nat} (hi : i < n) :
    (autoOf n σ τ)[σ[i]!]! = τ[i]! := by
  rw [autoOf]
  exact autoOf_foldl_get n σ τ (List.range n) List.nodup_range
    (fun x hx y hy => hσ.inj x (by simpa using hx) y (by simpa using hy)) _ (by simp) i
    (by simpa using hi) (hσ.lt i hi)

theorem autoOf_size (n : Nat) (σ τ : Array Nat) : (autoOf n σ τ).size = n := by
  rw [autoOf, autoOf_foldl_size]; simp

/-- `autoOf` of two permutation arrays is a permutation array. -/
theorem autoOf_permArr {n : Nat} {σ τ : Array Nat} (hσ : PermArr n σ) (hτ : PermArr n τ) :
    PermArr n (autoOf n σ τ) := by
  refine ⟨autoOf_size n σ τ, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hσ.surj hx
    rw [autoOf_get hσ hi]
    exact hτ.lt i hi
  · obtain ⟨i, hi, rfl⟩ := hσ.surj hx
    obtain ⟨j, hj, rfl⟩ := hσ.surj hy
    rw [autoOf_get hσ hi, autoOf_get hσ hj] at hxy
    rw [hτ.inj i hi j hj hxy]

/-- **Automorphism harvesting is correct.**  Two leaf labellings with the same certificate differ
by an automorphism, and `autoOf` computes it. -/
theorem autoOf_auto {n : Nat} {f : Nat → Nat → Bool} {σ τ : Array Nat} (hσ : PermArr n σ)
    (hτ : PermArr n τ) (hcert : certOf (Graph.ofOracle n f) σ = certOf (Graph.ofOracle n f) τ)
    {u v : Nat} (hu : u < n) (hv : v < n) :
    f (autoOf n σ τ)[u]! (autoOf n σ τ)[v]! = f u v := by
  obtain ⟨i, hi, rfl⟩ := hσ.surj hu
  obtain ⟨j, hj, rfl⟩ := hσ.surj hv
  have hn : (Graph.ofOracle n f).n = n := ofOracle_n n f
  have hi' : i < (Graph.ofOracle n f).n := by rw [hn]; exact hi
  have hj' : j < (Graph.ofOracle n f).n := by rw [hn]; exact hj
  have key := congrArg (fun c => certGet (Graph.ofOracle n f).n c i j) hcert
  rw [certOf_get (G := Graph.ofOracle n f) hi' hj',
    certOf_get (G := Graph.ofOracle n f) hi' hj'] at key
  rw [autoOf_get hσ hi, autoOf_get hσ hj]
  rw [ofOracle_adj n f _ _ (hτ.lt i hi) (hτ.lt j hj)] at key
  rw [ofOracle_adj n f _ _ (hσ.lt i hi) (hσ.lt j hj)] at key
  exact key.symm

/-! ### Automorphisms act on the search tree -/

/-- Oracles that agree on `{0, …, n-1}` build the same graph. -/
theorem ofOracle_congr {n : Nat} {f f' : Nat → Nat → Bool}
    (h : ∀ a, a < n → ∀ b, b < n → f a b = f' a b) :
    Graph.ofOracle n f = Graph.ofOracle n f' := by
  have hrow : ∀ v : Fin n, (fun w : Fin n => f v.1 w.1) = (fun w : Fin n => f' v.1 w.1) := by
    intro v; funext w; exact h v.1 v.2 w.1 w.2
  rw [Graph.ofOracle, Graph.ofOracle]
  simp only [Graph.mk.injEq, true_and]
  constructor
  · congr 1; funext v; rw [hrow v]
  · congr 1
    funext v
    refine Array.ext' ?_
    simp only [Array.toList_filter]
    refine List.filter_congr ?_
    intro x hx
    have hxn : x < n := by simpa using hx
    rw [h v.1 v.2 x hxn]

/-- `Reach` only looks at the oracle inside `{0, …, n-1}`. -/
theorem reach_congr {n : Nat} {f f' : Nat → Nat → Bool}
    (h : ∀ a, a < n → ∀ b, b < n → f a b = f' a b) {invPath : Array UInt64} {p : Part}
    {k : List (List UInt64)} (hr : Reach n f invPath p k) : Reach n f' invPath p k := by
  have hG : Graph.ofOracle n f = Graph.ofOracle n f' := ofOracle_congr h
  induction hr with
  | @leaf invPath p htc => rw [hG]; exact Reach.leaf htc
  | @step invPath p c v k hc hv hcell _ ih => rw [hG] at ih; exact Reach.step hc hv hcell ih

/-- `g` is an automorphism of `Graph.ofOracle n f`, in array form. -/
structure IsAutoArr (n : Nat) (f : Nat → Nat → Bool) (g : Array Nat) : Prop where
  /-- It permutes the vertices. -/
  perm : PermArr n g
  /-- It preserves adjacency. -/
  adj : ∀ u, u < n → ∀ v, v < n → f g[u]! g[v]! = f u v

/-- **What automorphism harvesting yields.** -/
theorem autoOf_isAuto {n : Nat} {f : Nat → Nat → Bool} {σ τ : Array Nat} (hσ : PermArr n σ)
    (hτ : PermArr n τ) (hcert : certOf (Graph.ofOracle n f) σ = certOf (Graph.ofOracle n f) τ) :
    IsAutoArr n f (autoOf n σ τ) :=
  ⟨autoOf_permArr hσ hτ, fun _ hu _ hv => autoOf_auto hσ hτ hcert hu hv⟩

/-- An automorphism does not change the graph it is an automorphism of. -/
theorem IsAutoArr.graph {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g) :
    Graph.ofOracle n (fun a b => f g[a]! g[b]!) = Graph.ofOracle n f :=
  ofOracle_congr fun a ha b hb => hg.adj a ha b hb

/-- **Automorphisms permute the leaves.**  If `p` is `γ`-invariant, transporting along `γ` sends
leaves below `p` to leaves below `p` with the same key. -/
theorem reach_auto {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g)
    {invPath : Array UInt64} {p q : Part} {k : List (List UInt64)} (hp : Part.WF n p)
    (hq : Part.WF n q) (he : PartEquiv n (fun x => g[x]!) p q) (h : Reach n f invPath q k) :
    Reach n f invPath p k :=
  reach_transfer hg.perm.isPerm
    (reach_congr (fun a ha b hb => (hg.adj a ha b hb).symm) h) hp hq he

theorem child_wf {n : Nat} {f : Nat → Nat → Bool} {p : Part} (hp : Part.WF n p) {v : Nat}
    (hv : v < n) : Part.WF n (child (Graph.ofOracle n f) p v).1 := by
  rw [child]
  exact refine_wf (individualize_wf' hp hv) _ _

/-- **Orbit pruning is sound.**  If `γ` is an automorphism fixing the current partition, the
subtree below the child `v` and the subtree below the child `γ v` have the same leaf keys. -/
theorem reach_child_auto {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g)
    {p : Part} (hp : Part.WF n p) (he : PartEquiv n (fun x => g[x]!) p p)
    {invPath : Array UInt64} {v : Nat} {k : List (List UInt64)} (hv : v < n)
    (h : Reach n f (childInv (Graph.ofOracle n f) invPath p v)
      (child (Graph.ofOracle n f) p v).1 k) :
    Reach n f (childInv (Graph.ofOracle n f) invPath p g[v]!)
      (child (Graph.ofOracle n f) p g[v]!).1 k := by
  have hG := hg.graph
  have hce := child_equiv (f := f) hg.perm.isPerm hp hp he hv
  have hci := childInv_equiv (f := f) hg.perm.isPerm hp hp he invPath hv
  rw [hG] at hce hci
  rw [hci]
  exact reach_auto hg (child_wf hp (hg.perm.lt v hv)) (child_wf hp hv) hce.1 h

end Canon
end IsoGraph
