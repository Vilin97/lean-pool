/-
Copyright (c) 2026 Tom Adamczewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Adamczewski
-/

module

public import LeanPool.Erdos548.Words
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Rooted tree copies supported on word prefixes

`attachLeaves S r s` adds `s` new pendant vertices at the vertex `r` of `S`, and a copy of `S`
in a host graph extends to a copy of `attachLeaves S r 1` whenever some neighbour of the image of
`r` is unused (`attach_single_leaf_copy`).

`RootedWordFamily S r G b X` says that `S` has a copy in `G` sending the root `r` to `b` and
every other vertex into `X`; `rootedWordCount S r G l₀` counts the cut permutation words of `l₀`
supporting such a copy on their prefix. Moving the root to a newly attached leaf costs at most
one word per permutation (`rooted_word_leaf_move_count`), and two rooted trees glued at a common
root satisfy the branch gluing inequality (`rooted_word_branch_gluing_count`).

Deleting the edge `rs` of a tree leaves two trees (`tree_edge_partition`), so a root of degree at
least two splits a finite tree into two strictly smaller rooted trees meeting only at the root
(`tree_root_partition`), and removing a leaf and re-attaching it is an isomorphism
(`leafRestoreIso`). A strong induction on the order `t` of the tree then proves
`rooted_word_tree_bound`: the adjacency-marked cut permutation words of a repetition-free host
word `l₀` number at most those supporting a rooted copy of the tree plus `(t - 2) · |l₀|!`.
-/

public section

open SimpleGraph

namespace Erdos548

/-! Attaching leaves to a graph. -/

/-- Attach a set of new leaves to a fixed vertex. -/
def attachLeaves {V : Type*} (S : SimpleGraph V) (r : V) (s : ℕ) :
    SimpleGraph (V ⊕ Fin s) where
  Adj
    | .inl a, .inl b => S.Adj a b
    | .inl a, .inr _ => a = r
    | .inr _, .inl b => b = r
    | .inr _, .inr _ => False
  symm := by constructor; rintro (a | a) (b | b) h <;> first | exact h.symm | exact h
  loopless := by constructor; rintro (a | a) <;> simp

lemma attach_single_leaf_copy {U V : Type*} (S : SimpleGraph U) (G : SimpleGraph V)
    (r : U) (f : S.Copy G) (w : V) (hw : G.Adj (f r) w) (hfree : w ∉ Set.range f) :
    ∃ F : (attachLeaves S r 1).Copy G,
      (∀ x, F (Sum.inl x) = f x) ∧ F (Sum.inr 0) = w := by
  classical
  let F : U ⊕ Fin 1 → V := Sum.elim f (fun _ => w)
  have hadj : ∀ x y, (attachLeaves S r 1).Adj x y → G.Adj (F x) (F y) := by
    rintro (x | x) (y | y) h
    · exact f.toHom.map_adj h
    · have he : x = r := h
      subst x
      exact hw
    · have he : y = r := h
      subst y
      exact hw.symm
    · exact h.elim
  have hinj : Function.Injective F := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (f.injective h)
    · exact (hfree ⟨x, h⟩).elim
    · exact (hfree ⟨y, h.symm⟩).elim
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  exact ⟨⟨⟨F, fun {x y} h => hadj x y h⟩, hinj⟩, fun _ => rfl, rfl⟩

/-! Rooted graph copies in permutation-word prefixes and the leaf-root move. -/

/-- A rooted copy supported on the root image and the displayed outer set. -/
@[expose] def RootedWordFamily {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (b : V) (X : Finset V) : Prop :=
  ∃ f : S.Copy G, f r = b ∧ ∀ x, f x ∈ insert b X

/-- The number of cut permutation words of `l₀` supporting a rooted copy of `S` with root at the
first letter. -/
@[expose] noncomputable def rootedWordCount {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (l₀ : List V) : ℕ :=
  fullWordCount l₀ G.Adj (RootedWordFamily S r G)

lemma rootedWordFamily_mono {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (b : V) {X Y : Finset V}
    (hXY : X ⊆ Y) : RootedWordFamily S r G b X → RootedWordFamily S r G b Y := by
  rintro ⟨f, hfr, hspan⟩
  exact ⟨f, hfr, fun x => (Finset.insert_subset_insert _ hXY) (hspan x)⟩

lemma rooted_word_leaf_move_step {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (l : List V) (hl : l.Nodup)
    (k : ℕ) (hk : k < l.length)
    (hs : FullWordQualifies G.Adj (RootedWordFamily S r G) l k)
    (j : ℕ) (hjk : j < k)
    (hj : FullWordQualifies G.Adj (RootedWordFamily S r G) l j) :
    FullWordQualifies G.Adj (RootedWordFamily (attachLeaves S r 1) (Sum.inr 0) G)
      (reverseWordAt l (k + 1)) k := by
  classical
  obtain ⟨b, q, rfl, hm, _⟩ := hs
  have hkq : k ≤ q.length := by simpa only [List.length_cons, Nat.lt_add_one_iff] using hk
  have hj' := (fullWordQualifies_cons G.Adj (RootedWordFamily S r G) b q j).mp hj
  obtain ⟨f, hfr, hspan⟩ := hj'.2
  obtain ⟨w, hw, hbw⟩ := hm
  obtain ⟨p, hp⟩ := List.getLast?_eq_some_iff.mp hw
  let z := q.drop k
  have hq : q = p ++ w::z := by
    have he := List.take_append_drop k q
    rw [hp] at he
    simpa only [List.append_assoc, List.singleton_append] using he.symm
  have hpk : p.length + 1 = k := by
    have he := congrArg List.length hp
    simp only [List.length_take, List.length_append, List.length_singleton] at he
    omega
  have hjp : j ≤ p.length := by omega
  have htakej : q.take j = p.take j := by
    rw [hq, List.take_append_of_le_length hjp]
  have hnq : q.Nodup := (List.nodup_cons.mp hl).2
  have hnd : (p ++ w::z).Nodup := hq ▸ hnq
  have hwP : w ∉ p := by
    intro hh
    exact (List.disjoint_left.mp hnd.disjoint) hh List.mem_cons_self
  have hfree : w ∉ Set.range f := by
    rintro ⟨x, hx⟩
    have hh := hspan x
    rw [hx] at hh
    rcases Finset.mem_insert.mp hh with he | he
    · exact hbw.ne he.symm
    · rw [htakej] at he
      exact hwP (List.mem_of_mem_take (List.mem_toFinset.mp he))
  obtain ⟨F, hF, hFw⟩ := attach_single_leaf_copy S G r f w (by rw [hfr]; exact hbw) hfree
  have hrev : reverseWordAt (b::q) (k + 1) = w::(p.reverse ++ b::z.reverse) := by
    rw [hq, ← hpk]
    simpa only [Nat.add_assoc] using reverseWordAt_decomposition b w p z
  have hnewtake : (p.reverse ++ b::z.reverse).take k = p.reverse ++ [b] := by
    have he : p.reverse ++ b::z.reverse = (p.reverse ++ [b]) ++ z.reverse := by
      simp only [List.append_assoc, List.singleton_append]
    have hlen : (p.reverse ++ [b]).length = k := by
      simp only [List.length_append, List.length_reverse, List.length_singleton]
      exact hpk
    rw [he, ← hlen, List.take_left]
  rw [hrev]
  apply (fullWordQualifies_cons G.Adj _ _ _ _).mpr
  constructor
  · rw [hnewtake]
    exact ⟨b, List.getLast?_concat, hbw.symm⟩
  · refine ⟨F, hFw, ?_⟩
    rintro (x | x)
    · rw [hF x, hnewtake]
      apply Finset.mem_insert_of_mem
      have hh := hspan x
      rcases Finset.mem_insert.mp hh with hx | hx
      · rw [hx]
        exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
      · rw [htakej] at hx
        apply List.mem_toFinset.mpr
        apply List.mem_append_left
        exact List.mem_reverse.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx))
    · have hx : x = 0 := Subsingleton.elim _ _
      subst x
      rw [hFw]
      exact Finset.mem_insert_self _ _

lemma rooted_word_leaf_move_count {U V : Type*} [DecidableEq V]
    (S : SimpleGraph U) (r : U) (G : SimpleGraph V) (l₀ : List V) (hl : l₀.Nodup) :
    rootedWordCount S r G l₀ ≤
      rootedWordCount (attachLeaves S r 1) (Sum.inr 0) G l₀ + (permutationWords l₀).card := by
  apply full_word_transfer_count
  intro l hlp k hk hs j hjk hj
  exact rooted_word_leaf_move_step S r G l (hlp.nodup_iff.mpr hl) k
    (by rwa [hlp.length_eq]) hs j hjk hj

lemma rootedWordFamily_iso_iff {U W V : Type*} [DecidableEq V]
    {S : SimpleGraph U} {T : SimpleGraph W} (e : S ≃g T) (r : U)
    (G : SimpleGraph V) (b : V) (X : Finset V) :
    RootedWordFamily T (e r) G b X ↔ RootedWordFamily S r G b X := by
  constructor
  · rintro ⟨f, hfr, hspan⟩
    exact ⟨f.comp e.toCopy, hfr, fun x => hspan (e x)⟩
  · rintro ⟨f, hfr, hspan⟩
    refine ⟨f.comp e.symm.toCopy, ?_, fun x => hspan (e.symm x)⟩
    simpa using hfr

lemma rootedWordCount_iso {U W V : Type*} [DecidableEq V]
    {S : SimpleGraph U} {T : SimpleGraph W} (e : S ≃g T) (r : U)
    (G : SimpleGraph V) (l₀ : List V) :
    rootedWordCount T (e r) G l₀ = rootedWordCount S r G l₀ := by
  have he : RootedWordFamily T (e r) G = RootedWordFamily S r G := by
    funext b X
    exact propext (rootedWordFamily_iso_iff e r G b X)
  unfold rootedWordCount
  rw [he]

lemma rootedWordFamily_restrict {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (G : SimpleGraph V) (A : Set U) (r : U) (hr : r ∈ A)
    (b : V) (X : Finset V) : RootedWordFamily T r G b X →
      RootedWordFamily (T.induce A) ⟨r, hr⟩ G b X := by
  rintro ⟨f, hfr, hspan⟩
  exact ⟨f.comp (Copy.induce T A), hfr, fun x => hspan x.val⟩

/-- Two copies agree at the root. Disjoint outer supporting sets ensure that
no other images collide. -/
lemma rootedWordFamily_glue {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (G : SimpleGraph V) (A : Set U) (r : U) (hr : r ∈ A)
    (hsep : ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x = r)
    (b : V) (R X : Finset V) (hd : Disjoint R X)
    (hf : RootedWordFamily (T.induce A) ⟨r, hr⟩ G b R)
    (hg : RootedWordFamily (T.induce (Aᶜ ∪ {r})) ⟨r, Or.inr rfl⟩ G b X) :
    RootedWordFamily T r G b (R ∪ X) := by
  classical
  obtain ⟨f, hfr, hfspan⟩ := hf
  obtain ⟨g, hgr, hgspan⟩ := hg
  let F : U → V := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else g ⟨x, Or.inl hx⟩
  have hcross : ∀ x : A, ∀ y : (Aᶜ ∪ {r} : Set U), y.val ∉ A → f x ≠ g y := by
    intro x y hy he
    have hgneq : g y ≠ b := by
      intro hb
      have hy' : y = ⟨r, Or.inr rfl⟩ := g.injective (hb.trans hgr.symm)
      exact hy (by simpa only [hy'] using hr)
    have hfR : f x ∈ R :=
      (Finset.mem_insert.mp (hfspan x)).resolve_left (fun hh => hgneq (he.symm.trans hh))
    have hgX : g y ∈ X := (Finset.mem_insert.mp (hgspan y)).resolve_left hgneq
    exact Finset.disjoint_left.mp hd hfR (he.symm ▸ hgX)
  have hmap : ∀ {x y}, T.Adj x y → G.Adj (F x) (F y) := by
    intro x y hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · simpa only [F, dite_eq_left hx, dite_eq_left hy] using
        (show G.Adj (f ⟨x, hx⟩) (f ⟨y, hy⟩) from f.toHom.map_adj hxy)
    · have hxr := hsep x hx y hy hxy
      subst x
      have he := g.toHom.map_adj (show (T.induce (Aᶜ ∪ {r})).Adj
        ⟨r, Or.inr rfl⟩ ⟨y, Or.inl hy⟩ from hxy)
      change G.Adj (g ⟨r, Or.inr rfl⟩) (g ⟨y, Or.inl hy⟩) at he
      simpa only [F, dite_eq_left hr, dite_eq_right hy, hfr, hgr] using he
    · have hyr := hsep y hy x hx hxy.symm
      subst y
      have he := g.toHom.map_adj (show (T.induce (Aᶜ ∪ {r})).Adj
        ⟨x, Or.inl hx⟩ ⟨r, Or.inr rfl⟩ from hxy)
      change G.Adj (g ⟨x, Or.inl hx⟩) (g ⟨r, Or.inr rfl⟩) at he
      simpa only [F, dite_eq_right hx, dite_eq_left hr, hfr, hgr] using he
    · simpa only [F, dite_eq_right hx, dite_eq_right hy] using
        (show G.Adj (g ⟨x, Or.inl hx⟩) (g ⟨y, Or.inl hy⟩) from g.toHom.map_adj hxy)
  have hinj : Function.Injective F := by
    intro x y he
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · have he' : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
        simpa only [F, dite_eq_left hx, dite_eq_left hy] using he
      exact congrArg Subtype.val (f.injective he')
    · exact (hcross ⟨x, hx⟩ ⟨y, Or.inl hy⟩ hy
        (by simpa only [F, dite_eq_left hx, dite_eq_right hy] using he)).elim
    · exact (hcross ⟨y, hy⟩ ⟨x, Or.inl hx⟩ hx
        (by simpa only [F, dite_eq_right hx, dite_eq_left hy] using he.symm)).elim
    · have he' : g ⟨x, Or.inl hx⟩ = g ⟨y, Or.inl hy⟩ := by
        simpa only [F, dite_eq_right hx, dite_eq_right hy] using he
      exact congrArg Subtype.val (g.injective he')
  refine ⟨⟨⟨F, hmap⟩, hinj⟩, ?_, ?_⟩
  · change F r = b
    simpa only [F, dite_eq_left hr] using hfr
  · intro x
    by_cases hx : x ∈ A
    · change F x ∈ _
      rw [show F x = f ⟨x, hx⟩ by simp only [F, dite_eq_left hx]]
      exact Finset.insert_subset_insert b Finset.subset_union_left (hfspan ⟨x, hx⟩)
    · change F x ∈ _
      rw [show F x = g ⟨x, Or.inl hx⟩ by simp only [F, dite_eq_right hx]]
      exact Finset.insert_subset_insert b Finset.subset_union_right (hgspan ⟨x, Or.inl hx⟩)

lemma rooted_word_branch_gluing_count {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (G : SimpleGraph V) (A : Set U) (r : U) (hr : r ∈ A)
    (hsep : ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x = r)
    (l₀ : List V) (hl : l₀.Nodup) (hne : l₀ ≠ []) :
    rootedWordCount (T.induce A) ⟨r, hr⟩ G l₀ +
      rootedWordCount (T.induce (Aᶜ ∪ {r})) ⟨r, Or.inr rfl⟩ G l₀ ≤
      fullWordCount l₀ G.Adj (fun _ _ => True) + (permutationWords l₀).card +
        rootedWordCount T r G l₀ := by
  apply full_word_gluing_count l₀ hl hne
  · exact rootedWordFamily_restrict T G A r hr
  · exact rootedWordFamily_glue T G A r hr hsep

/-! Splitting finite trees at an edge or at a root. -/

lemma tree_edge_partition {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    (r s : U) (hrs : T.Adj r s) :
    ∃ A : Set U, r ∈ A ∧ s ∉ A ∧ (T.induce A).IsTree ∧ (T.induce Aᶜ).IsTree ∧
      ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x = r ∧ y = s := by
  classical
  let D := T \ fromEdgeSet {s(r, s)}
  have hno : ¬D.Reachable r s :=
    isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hrs)
  have hdeleted : ∀ {x y}, T.Adj x y → ¬D.Adj x y →
      (x = r ∧ y = s) ∨ (x = s ∧ y = r) := by
    intro x y hxy hn
    have he : s(x, y) = s(r, s) := by
      by_contra he
      apply hn
      exact ⟨hxy, by simp [fromEdgeSet_adj, he]⟩
    exact Sym2.eq_iff.mp he
  have hwalk : ∀ {x y} (p : T.Walk x y),
      (D.Reachable r y ∨ D.Reachable s y) → (D.Reachable r x ∨ D.Reachable s x) := by
    intro x y p
    induction p with
    | nil => exact fun h => h
    | @cons x y z hxy p ih =>
      intro h
      have hy := ih h
      by_cases he : D.Adj x y
      · exact hy.elim (fun h => Or.inl (h.trans he.symm.reachable))
          (fun h => Or.inr (h.trans he.symm.reachable))
      · rcases hdeleted hxy he with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact Or.inl Reachable.rfl
        · exact Or.inr Reachable.rfl
  have hcover : ∀ x, D.Reachable r x ∨ D.Reachable s x := by
    intro x
    obtain ⟨p⟩ := hT.connected.preconnected x r
    exact hwalk p (Or.inl Reachable.rfl)
  let A := (D.connectedComponentMk r).supp
  have hmem : ∀ x, x ∈ A ↔ D.Reachable r x := by
    intro x
    simp only [A, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, D.reachable_comm]
  have hrA : r ∈ A := (hmem r).mpr Reachable.rfl
  have hsA : s ∉ A := fun h => hno ((hmem s).mp h)
  have hAc : Aᶜ = (D.connectedComponentMk s).supp := by
    ext x
    simp only [Set.mem_compl_iff, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    constructor
    · intro hx
      exact ((hcover x).resolve_left (fun h => hx ((hmem x).mpr h))).symm
    · intro hx hxa
      exact hno (((hmem x).mp hxa).trans hx)
  have hAconn : (T.induce A).Connected :=
    Connected.mono (show D.induce A ≤ T.induce A from fun _ _ h => h.1)
      (D.connectedComponentMk r).connected_toSimpleGraph
  have hAcconn : (T.induce Aᶜ).Connected := by
    rw [hAc]
    exact Connected.mono (show D.induce (D.connectedComponentMk s).supp ≤
      T.induce (D.connectedComponentMk s).supp from fun _ _ h => h.1)
      (D.connectedComponentMk s).connected_toSimpleGraph
  refine ⟨A, hrA, hsA, ⟨hAconn, hT.isAcyclic.induce A⟩,
    ⟨hAcconn, hT.isAcyclic.induce Aᶜ⟩, ?_⟩
  intro x hx y hy hxy
  have hn : ¬D.Adj x y := by
    intro h
    exact hy ((hmem y).mpr (((hmem x).mp hx).trans h.reachable))
  rcases hdeleted hxy hn with h | ⟨rfl, rfl⟩
  · exact h
  · exact (hsA hx).elim

lemma tree_root_partition {U : Type} [Finite U] (T : SimpleGraph U) (hT : T.IsTree)
    (r s z : U) (hrs : T.Adj r s) (hrz : T.Adj r z) (hsz : s ≠ z) :
    ∃ A : Set U, ∃ _hr : r ∈ A,
      (T.induce A).IsTree ∧ (T.induce (Aᶜ ∪ {r})).IsTree ∧
      2 ≤ Nat.card A ∧ 2 ≤ Nat.card (Aᶜ ∪ {r} : Set U) ∧
      Nat.card A < Nat.card U ∧ Nat.card (Aᶜ ∪ {r} : Set U) < Nat.card U ∧
      Nat.card A + Nat.card (Aᶜ ∪ {r} : Set U) = Nat.card U + 1 ∧
      ∀ x ∈ A, ∀ y ∉ A, T.Adj x y → x = r := by
  classical
  obtain ⟨A, hr, hs, hA, hAc, hcut⟩ := tree_edge_partition T hT r s hrs
  have hz : z ∈ A := by
    by_contra hz
    exact hsz (hcut r hr z hz hrz).2.symm
  have hB : (T.induce (Aᶜ ∪ {r})).IsTree := by
    exact ⟨connected_induce_union hAc.connected.preconnected
      Preconnected.of_subsingleton hs (Set.mem_singleton r) hrs.symm,
      hT.isAcyclic.induce _⟩
  have hA2 : 2 ≤ A.ncard := by
    have hh : ({r, z} : Set U) ⊆ A := by
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff] using And.intro hr hz
    simpa only [Set.ncard_pair hrz.ne] using Set.ncard_le_ncard hh
  have hB2 : 2 ≤ (Aᶜ ∪ {r}).ncard := by
    have hh : ({s, r} : Set U) ⊆ Aᶜ ∪ {r} := by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      exact ⟨Or.inl hs, Or.inr trivial⟩
    simpa only [Set.ncard_pair hrs.ne.symm] using Set.ncard_le_ncard hh
  have hAlt : A.ncard < Nat.card U := Set.ncard_lt_card (by
    intro he
    exact hs (he ▸ Set.mem_univ s))
  have hBlt : (Aᶜ ∪ {r}).ncard < Nat.card U := Set.ncard_lt_card (by
    intro he
    have hm : z ∈ Aᶜ ∪ {r} := he ▸ Set.mem_univ z
    exact hm.elim (fun hh => hh hz) hrz.ne.symm)
  have hcard : A.ncard + (Aᶜ ∪ {r}).ncard = Nat.card U + 1 := by
    rw [Set.union_singleton, Set.ncard_insert_of_notMem (by simpa using hr)]
    rw [← Nat.add_assoc, Set.ncard_add_ncard_compl]
  exact ⟨A, hr, hA, hB, hA2, hB2, hAlt, hBlt, hcard, fun x hx y hy hxy => (hcut x hx y hy hxy).1⟩

/-- Removing a leaf `l` with unique neighbour `p` and attaching one new leaf at `p` gives back
the original graph, up to isomorphism. -/
noncomputable def leafRestoreIso {U : Type} (T : SimpleGraph U) (l p : U)
    (hlp : T.Adj l p) (honly : ∀ x, T.Adj l x → x = p) :
    attachLeaves (T.induce {l}ᶜ) ⟨p, hlp.ne.symm⟩ 1 ≃g T := by
  classical
  let f : ({l}ᶜ : Set U) ⊕ Fin 1 → U := Sum.elim Subtype.val (fun _ => l)
  let g : U → ({l}ᶜ : Set U) ⊕ Fin 1 := fun x => if hx : x = l then Sum.inr 0 else Sum.inl ⟨x, hx⟩
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases hx : x = l <;> simp [f, g, hx]
  have hgf : Function.LeftInverse g f := by
    rintro (x | x)
    · have hx : x.val ≠ l := x.property
      simp only [f, Sum.elim_inl, g, dite_eq_right hx]
    · have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp only [f, Sum.elim_inr, g, dite_eq_left rfl]
  refine ⟨⟨f, g, hgf, hfg⟩, ?_⟩
  rintro (x | x) (y | y)
  · rfl
  · change T.Adj x.val l ↔ x = ⟨p, hlp.ne.symm⟩
    constructor
    · exact fun h => Subtype.ext (honly x.val h.symm)
    · intro h
      rw [h]
      exact hlp.symm
  · change T.Adj l y.val ↔ y = ⟨p, hlp.ne.symm⟩
    constructor
    · exact fun h => Subtype.ext (honly y.val h)
    · intro h
      rw [h]
      exact hlp
  · change T.Adj l l ↔ False
    simp

@[simp] lemma leafRestoreIso_inl {U : Type} (T : SimpleGraph U) (l p : U)
    (hlp : T.Adj l p) (honly : ∀ x, T.Adj l x → x = p) (x : ({l}ᶜ : Set U)) :
    leafRestoreIso T l p hlp honly (Sum.inl x) = x.val := by rfl

@[simp] lemma leafRestoreIso_inr {U : Type} (T : SimpleGraph U) (l p : U)
    (hlp : T.Adj l p) (honly : ∀ x, T.Adj l x → x = p) :
    leafRestoreIso T l p hlp honly (Sum.inr 0) = l := by rfl

/-! The rooted word-count bound for every finite tree. -/

lemma rootedWordFamily_of_card_two {U V : Type*} [Fintype U] [DecidableEq V]
    (T : SimpleGraph U) (r : U) (ht : Fintype.card U = 2)
    (G : SimpleGraph V) (b w : V) (hbw : G.Adj b w) (X : Finset V) (hw : w ∈ X) :
    RootedWordFamily T r G b X := by
  classical
  have hc : Fintype.card ({r}ᶜ : Set U) ≤ 1 := by
    rw [Fintype.card_compl_set, ht]
    simp
  have : Subsingleton ({r}ᶜ : Set U) := Fintype.card_le_one_iff_subsingleton.mp hc
  have hnonroot : ∀ x y : U, x ≠ r → y ≠ r → x = y := by
    intro x y hx hy
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ({r}ᶜ : Set U)) ⟨y, hy⟩)
  let F : U → V := fun x => if x = r then b else w
  have hinj : Function.Injective F := by
    intro x y he
    by_cases hx : x = r <;> by_cases hy : y = r
    · exact hx.trans hy.symm
    · exact (hbw.ne (by simpa only [F, ite_eq_left hx, ite_eq_right hy] using he)).elim
    · exact (hbw.ne.symm (by simpa only [F, ite_eq_right hx, ite_eq_left hy] using he)).elim
    · exact hnonroot x y hx hy
  have hadj : ∀ {x y}, T.Adj x y → G.Adj (F x) (F y) := by
    intro x y hxy
    by_cases hx : x = r <;> by_cases hy : y = r
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · simpa only [F, ite_eq_left hx, ite_eq_right hy] using hbw
    · simpa only [F, ite_eq_right hx, ite_eq_left hy] using hbw.symm
    · exact (hxy.ne (hnonroot x y hx hy)).elim
  refine ⟨⟨⟨F, hadj⟩, hinj⟩, ?_, ?_⟩
  · change F r = b
    simp only [F, ite_eq_left rfl]
  · intro x
    change F x ∈ _
    by_cases hx : x = r
    · simp only [F, ite_eq_left hx, Finset.mem_insert_self]
    · simpa only [F, ite_eq_right hx] using Finset.mem_insert_of_mem hw

lemma rooted_word_count_base {U V : Type*} [Fintype U] [DecidableEq V]
    (T : SimpleGraph U) (r : U) (ht : Fintype.card U = 2)
    (G : SimpleGraph V) (l₀ : List V) :
    fullWordCount l₀ G.Adj (fun _ _ => True) ≤ rootedWordCount T r G l₀ := by
  classical
  rw [fullWordCount_eq_card, rootedWordCount, fullWordCount_eq_card]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hl, hk, b, q, he, hm, _⟩ := (mem_fullGoodWordCuts _ _ _ _ _).mp hp
  obtain ⟨w, hw, hbw⟩ := hm
  refine (mem_fullGoodWordCuts _ _ _ _ _).mpr ⟨hl, hk, b, q, he, ⟨w, hw, hbw⟩, ?_⟩
  apply rootedWordFamily_of_card_two T r ht G b w hbw
  exact List.mem_toFinset.mpr
    (List.mem_of_mem_getLast? (by simpa only [hw] using (show w ∈ some w from rfl)))

lemma rooted_word_tree_bound_aux (t : ℕ) :
    ∀ (U V : Type) [Fintype U] [DecidableEq V]
      (T : SimpleGraph U) (r : U) (_hT : T.IsTree) (_ht : Fintype.card U = t) (_ht2 : 2 ≤ t)
      (G : SimpleGraph V) (l₀ : List V) (_hl : l₀.Nodup) (_hne : l₀ ≠ []),
      fullWordCount l₀ G.Adj (fun _ _ => True) ≤
        rootedWordCount T r G l₀ + (t - 2) * (permutationWords l₀).card := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro U V _ _ T r hT ht ht2 G l₀ hl hne
    classical
    by_cases htbase : t = 2
    · have hcard2 : Fintype.card U = 2 := ht.trans htbase
      simpa only [htbase, Nat.sub_self, Nat.zero_mul, Nat.add_zero] using
        rooted_word_count_base T r hcard2 G l₀
    have ht3 : 3 ≤ t := by omega
    have : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨s, hrs⟩ := hT.connected.preconnected.exists_adj_of_nontrivial r
    by_cases hleaf : ∀ z, T.Adj r z → z = s
    · have hdeg : T.degree r = 1 := degree_eq_one_iff_existsUnique_adj.mpr ⟨s, hrs, hleaf⟩
      let A : Set U := {r}ᶜ
      let a : A := ⟨s, hrs.ne.symm⟩
      have hTA : (T.induce A).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg, hT.isAcyclic.induce A⟩
      have hcard : Fintype.card A = t - 1 := by
        simp only [A, Fintype.card_compl_set, Fintype.card_unique, ht]
      have hsmall : Fintype.card A < t := by omega
      have htwo : 2 ≤ Fintype.card A := by omega
      have hbound := ih (Fintype.card A) hsmall A V (T.induce A) a hTA rfl htwo G l₀ hl hne
      have hmove := rooted_word_leaf_move_count (T.induce A) a G l₀ hl
      have hiso := rootedWordCount_iso (leafRestoreIso T r s hrs hleaf) (Sum.inr 0) G l₀
      rw [leafRestoreIso_inr] at hiso
      change rootedWordCount T r G l₀ =
        rootedWordCount (attachLeaves (T.induce A) a 1) (Sum.inr 0) G l₀ at hiso
      rw [← hiso] at hmove
      have hcoeff : Fintype.card A - 2 + 1 = t - 2 := by omega
      have hcost := congrArg (fun j => j * (permutationWords l₀).card) hcoeff
      simp only [Nat.add_mul, Nat.one_mul] at hcost
      omega
    · push Not at hleaf
      obtain ⟨z, hrz, hzs⟩ := hleaf
      obtain ⟨A, hr, hA, hB, hA2, hB2, hAlt, hBlt, hcard, hsep⟩ :=
        tree_root_partition T hT r s z hrs hrz hzs.symm
      simp only [Nat.card_eq_fintype_card, ht] at hAlt hBlt hcard
      simp only [Nat.card_eq_fintype_card] at hA2 hB2
      have hboundA := ih (Fintype.card A) hAlt A V (T.induce A) ⟨r, hr⟩ hA rfl hA2 G l₀ hl hne
      have hboundB := ih (Fintype.card (Aᶜ ∪ {r} : Set U)) hBlt (Aᶜ ∪ {r} : Set U) V
        (T.induce (Aᶜ ∪ {r})) ⟨r, Or.inr rfl⟩ hB rfl hB2 G l₀ hl hne
      have hglue := rooted_word_branch_gluing_count T G A r hr hsep l₀ hl hne
      have hcoeff : (Fintype.card A - 2) + (Fintype.card (Aᶜ ∪ {r} : Set U) - 2) + 1 = t - 2 := by
        omega
      have hcost := congrArg (fun j => j * (permutationWords l₀).card) hcoeff
      simp only [Nat.add_mul, Nat.one_mul] at hcost
      omega

lemma rooted_word_tree_bound {U V : Type} [Fintype U] [DecidableEq V]
    (T : SimpleGraph U) (r : U) (hT : T.IsTree) (ht2 : 2 ≤ Fintype.card U)
    (G : SimpleGraph V) (l₀ : List V) (hl : l₀.Nodup) (hne : l₀ ≠ []) :
    fullWordCount l₀ G.Adj (fun _ _ => True) ≤
      rootedWordCount T r G l₀ + (Fintype.card U - 2) * (permutationWords l₀).card :=
  rooted_word_tree_bound_aux (Fintype.card U) U V T r hT rfl ht2 G l₀ hl hne

end Erdos548
