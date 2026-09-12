/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import Mathlib

/-!
# Spread perfect matchings in Dirac graphs

Let `N` be a finite set of vertices of even cardinality in a simple graph `G`, and suppose that
the *Dirac condition with slack `t`* holds: every vertex of `N` has at least `|N| / 2 + t`
neighbours inside `N`.

Deleting the edges of a perfect matching of `N` drops each such degree by exactly one, so Dirac's
theorem can be applied `t + 1` times in a row: `G` contains `t + 1` perfect matchings of `N` which
are pairwise edge-disjoint (`SimpleGraph.exists_involutions_pairwise_ne`).  Averaging over these
`t + 1` matchings, one of them has weight at most a `1 / (t + 1)` fraction of the total weight
against any prescribed nonnegative weight function: this is the *spread* property recorded in
`SimpleGraph.exists_spread_involution`, and it is a deterministic substitute for the usual
"a random perfect matching is spread" argument.

## Main results

* `SimpleGraph.exists_involution_adj`: **Dirac's theorem for perfect matchings**, in the form of a
  fixed-point-free involution of `N` all of whose orbits are edges of `G`.
* `SimpleGraph.exists_isPerfectMatching_of_card_le_minDegree`: Dirac's theorem for a finite graph
  with an even number of vertices, phrased with `SimpleGraph.Subgraph.IsPerfectMatching`.
* `SimpleGraph.exists_involutions_pairwise_ne`: the Dirac condition with slack `t` produces `t + 1`
  pairwise edge-disjoint perfect matchings of `N`.
* `SimpleGraph.exists_spread_involution`: the Dirac condition with slack `t` produces a perfect
  matching of `N` of weight at most `1 / (t + 1)` times the total weight.

## Implementation notes

Perfect matchings of a finite set `N` of vertices are presented as *partner involutions*: functions
`f : V → V` mapping `N` to itself, involutive on `N`, without fixed points on `N`, and with
`G.Adj a (f a)` for every `a ∈ N`.  This presentation makes both edge-disjointness (`f i a ≠ f j a`)
and the weight of a matching (`∑ y ∈ N, w y (f y)`) easy to state.  The translation to
`SimpleGraph.Subgraph.IsPerfectMatching` is `SimpleGraph.exists_isPerfectMatching_of_involutive`.

Dirac's theorem itself is proved from scratch, by the standard maximum-matching argument: if a
matching of maximum size misses two vertices `u`, `v`, then all neighbours of `u` and of `v` are
matched, and no matched edge `x, f x` has `u` adjacent to `x` and `v` adjacent to `f x` (otherwise
the matching could be augmented), so the partner involution injects the neighbourhood of `u` into
the complement of the neighbourhood of `v`, contradicting the degree hypothesis.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V]

/-! ### Matchings of a finite vertex set, as partner involutions -/

section Aux

variable {A : Finset (Sym2 V)} {N S : Finset V} {f : V → V}

/-- The neighbours of `v` inside `N` with respect to the edge set `A`. -/
private def nbhdOn (A : Finset (Sym2 V)) (N : Finset V) (v : V) : Finset V :=
  (N.filter fun z => s(v, z) ∈ A).erase v

/-- Membership in `nbhdOn`: the neighbours of `v` inside `N` are the vertices `z ≠ v` of `N`
joined to `v` by an edge of `A`. -/
private theorem mem_nbhdOn {v z : V} : z ∈ nbhdOn A N v ↔ z ≠ v ∧ z ∈ N ∧ s(v, z) ∈ A := by
  simp [nbhdOn]

/-- Neighbourhoods inside `N` are contained in `N`. -/
private theorem nbhdOn_subset {v : V} : nbhdOn A N v ⊆ N := fun _ hz => (mem_nbhdOn.1 hz).2.1

/-- `f` is a partner involution matching the vertices of `S` to each other along edges of `A`
that land inside `N`. -/
private structure IsMatchingOn (A : Finset (Sym2 V)) (N S : Finset V) (f : V → V) : Prop where
  /-- `f` maps `S` to itself. -/
  mapsTo : ∀ a ∈ S, f a ∈ S
  /-- `f` is involutive on `S`. -/
  invol : ∀ a ∈ S, f (f a) = a
  /-- `f` has no fixed point on `S`. -/
  ne : ∀ a ∈ S, f a ≠ a
  /-- Each vertex of `S` is joined to its partner by an edge of `A` inside `N`. -/
  adj : ∀ a ∈ S, f a ∈ nbhdOn A N a

omit [DecidableEq V] in
/-- A finite set carrying a fixed-point-free involution has even cardinality. -/
private theorem even_card_of_involutive {f : V → V} :
    ∀ S : Finset V, (∀ a ∈ S, f a ∈ S) → (∀ a ∈ S, f (f a) = a) → (∀ a ∈ S, f a ≠ a) →
      Even S.card := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hmap hinv hne
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · have hfa : f a ∈ S := hmap a ha
      have hafa : f a ≠ a := hne a ha
      have hTsub : (S.erase a).erase (f a) ⊂ S :=
        Finset.ssubset_of_subset_of_ssubset (erase_subset _ _) (erase_ssubset ha)
      have hmem : ∀ b ∈ (S.erase a).erase (f a), b ∈ S := fun b hb =>
        mem_of_mem_erase (mem_of_mem_erase hb)
      have hmapT : ∀ b ∈ (S.erase a).erase (f a), f b ∈ (S.erase a).erase (f a) := by
        intro b hb
        have hbS : b ∈ S := hmem b hb
        rw [mem_erase, mem_erase] at hb ⊢
        refine ⟨fun h => hb.2.1 ?_, fun h => hb.1 ?_, hmap b hbS⟩
        · have h2 : f (f b) = f (f a) := by rw [h]
          rwa [hinv b hbS, hinv a ha] at h2
        · have h2 : f (f b) = f a := by rw [h]
          rwa [hinv b hbS] at h2
      have hcard : S.card = ((S.erase a).erase (f a)).card + 2 := by
        rw [card_erase_of_mem (mem_erase.2 ⟨hafa, hfa⟩), card_erase_of_mem ha]
        have : 1 < S.card := one_lt_card.2 ⟨a, ha, f a, hfa, fun h => hafa h.symm⟩
        omega
      have := ih _ hTsub hmapT (fun b hb => hinv b (hmem b hb)) fun b hb => hne b (hmem b hb)
      rw [hcard]
      exact this.add even_two

/-- Extending a matching by a new edge both of whose endpoints are unmatched. -/
private theorem isMatchingOn_insert_insert {u v : V} (hM : IsMatchingOn A N S f)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v) (hadj : v ∈ nbhdOn A N u) (huN : u ∈ N) :
    IsMatchingOn A N (insert u (insert v S)) (fun z => if z = u then v else if z = v then u
      else f z) := by
  have hvN : v ∈ N := (mem_nbhdOn.1 hadj).2.1
  have hsymm : u ∈ nbhdOn A N v :=
    mem_nbhdOn.2 ⟨huv, huN, by rw [Sym2.eq_swap]; exact (mem_nbhdOn.1 hadj).2.2⟩
  set g : V → V := fun z => if z = u then v else if z = v then u else f z with hg
  have hgu : g u = v := by simp [hg]
  have hgv : g v = u := by simp [hg, huv.symm]
  have hgS : ∀ a ∈ S, g a = f a := by
    intro a ha
    have h1 : a ≠ u := fun h => hu (h ▸ ha)
    have h2 : a ≠ v := fun h => hv (h ▸ ha)
    simp [hg, h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a ha
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu]; exact mem_insert_of_mem (mem_insert_self _ _)
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv]; exact mem_insert_self _ _
    · rw [hgS a ha']; exact mem_insert_of_mem (mem_insert_of_mem (hM.mapsTo a ha'))
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu, hgv]
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv, hgu]
    · rw [hgS a ha', hgS _ (hM.mapsTo a ha')]; exact hM.invol a ha'
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu]; exact huv.symm
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv]; exact huv
    · rw [hgS a ha']; exact hM.ne a ha'
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu]; exact hadj
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv]; exact hsymm
    · rw [hgS a ha']; exact hM.adj a ha'

/-- Augmenting a matching along a path `u - x - f x - v` with `u` and `v` unmatched. -/
private theorem isMatchingOn_augment {u v x : V} (hM : IsMatchingOn A N S f)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v) (hx : x ∈ S)
    (hux : x ∈ nbhdOn A N u) (hvx : f x ∈ nbhdOn A N v) (huN : u ∈ N) (hvN : v ∈ N) :
    IsMatchingOn A N (insert u (insert v S))
      (fun z => if z = u then x else if z = x then u else if z = v then f x
        else if z = f x then v else f z) := by
  have hfx : f x ∈ S := hM.mapsTo x hx
  have hxfx : f x ≠ x := hM.ne x hx
  have hxu : x ≠ u := fun h => hu (h ▸ hx)
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have hfxu : f x ≠ u := fun h => hu (h ▸ hfx)
  have hfxv : f x ≠ v := fun h => hv (h ▸ hfx)
  have hxu' : u ∈ nbhdOn A N x :=
    mem_nbhdOn.2 ⟨hxu.symm, huN, by rw [Sym2.eq_swap]; exact (mem_nbhdOn.1 hux).2.2⟩
  have hfxv' : v ∈ nbhdOn A N (f x) :=
    mem_nbhdOn.2 ⟨hfxv.symm, hvN, by rw [Sym2.eq_swap]; exact (mem_nbhdOn.1 hvx).2.2⟩
  set g : V → V := fun z => if z = u then x else if z = x then u else if z = v then f x
    else if z = f x then v else f z with hg
  have hgu : g u = x := by simp [hg]
  have hgx : g x = u := by simp [hg, hxu]
  have hgv : g v = f x := by simp [hg, huv.symm, hxv.symm]
  have hgfx : g (f x) = v := by simp [hg, hfxu, hxfx, hfxv]
  have hgS : ∀ a ∈ S, a ≠ x → a ≠ f x → g a = f a := by
    intro a ha h1 h2
    have h3 : a ≠ u := fun h => hu (h ▸ ha)
    have h4 : a ≠ v := fun h => hv (h ▸ ha)
    simp [hg, h1, h2, h3, h4]
  have hcases : ∀ a ∈ S, a ≠ x → a ≠ f x → (f a ≠ x ∧ f a ≠ f x) := by
    intro a ha h1 h2
    refine ⟨fun h => h2 ?_, fun h => h1 ?_⟩
    · rw [← hM.invol a ha, h]
    · rw [← hM.invol a ha, h, hM.invol x hx]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a ha
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu]; exact mem_insert_of_mem (mem_insert_of_mem hx)
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv]; exact mem_insert_of_mem (mem_insert_of_mem hfx)
    by_cases h1 : a = x
    · subst h1; rw [hgx]; exact mem_insert_self _ _
    by_cases h2 : a = f x
    · subst h2; rw [hgfx]; exact mem_insert_of_mem (mem_insert_self _ _)
    · rw [hgS a ha' h1 h2]
      exact mem_insert_of_mem (mem_insert_of_mem (hM.mapsTo a ha'))
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu, hgx]
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv, hgfx]
    by_cases h1 : a = x
    · subst h1; rw [hgx, hgu]
    by_cases h2 : a = f x
    · subst h2; rw [hgfx, hgv]
    · obtain ⟨e1, e2⟩ := hcases a ha' h1 h2
      rw [hgS a ha' h1 h2, hgS _ (hM.mapsTo a ha') e1 e2]
      exact hM.invol a ha'
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu]; exact hxu
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv]; exact hfxv
    by_cases h1 : a = x
    · subst h1; rw [hgx]; exact hxu.symm
    by_cases h2 : a = f x
    · subst h2; rw [hgfx]; exact hfxv.symm
    · rw [hgS a ha' h1 h2]; exact hM.ne a ha'
  · rcases mem_insert.1 ha with rfl | ha'
    · rw [hgu]; exact hux
    rcases mem_insert.1 ha' with rfl | ha'
    · rw [hgv]; exact hvx
    by_cases h1 : a = x
    · subst h1; rw [hgx]; exact hxu'
    by_cases h2 : a = f x
    · subst h2; rw [hgfx]; exact hfxv'
    · rw [hgS a ha' h1 h2]; exact hM.adj a ha'

/-- **Dirac's theorem**, edge-set form: if every vertex of an even set `N` has at least `|N| / 2`
neighbours in `N`, then `N` has a perfect matching. -/
private theorem exists_isMatchingOn (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 ≤ (nbhdOn A N v).card) :
    ∃ f : V → V, IsMatchingOn A N N f := by
  classical
  obtain ⟨S, hSmem, hSmax⟩ :=
    (N.powerset.filter fun S => ∃ f, IsMatchingOn A N S f).exists_max_image Finset.card
      ⟨∅, by
        refine mem_filter.2 ⟨mem_powerset.2 (empty_subset _), id, ?_, ?_, ?_, ?_⟩ <;> simp⟩
  obtain ⟨hSN, f, hf⟩ := by simpa [mem_powerset] using mem_filter.1 hSmem
  -- extending a matching by two unmatched vertices contradicts maximality
  have hbig : ∀ (u v : V) (g : V → V), u ∉ S → v ∉ S → u ≠ v → u ∈ N → v ∈ N →
      IsMatchingOn A N (insert u (insert v S)) g → False := by
    intro u v g hu hv huv huN hvN hg
    have hmem : insert u (insert v S) ∈ N.powerset.filter fun S => ∃ f, IsMatchingOn A N S f :=
      mem_filter.2 ⟨mem_powerset.2 (insert_subset huN (insert_subset hvN hSN)), g, hg⟩
    have hcard : (insert u (insert v S)).card = S.card + 2 := by
      rw [card_insert_of_notMem (by simp [huv, hu]), card_insert_of_notMem hv]
    have := hSmax _ hmem
    omega
  suffices hSeq : S = N by exact ⟨f, hSeq ▸ hf⟩
  by_contra hSne
  -- two unmatched vertices exist, by parity
  have hSlt : S.card < N.card :=
    card_lt_card ⟨hSN, fun h => hSne (Subset.antisymm hSN h)⟩
  have hSeven : Even S.card := even_card_of_involutive S hf.mapsTo hf.invol hf.ne
  have hdiff : 1 < (N \ S).card := by
    rw [card_sdiff, inter_eq_left.2 hSN]
    obtain ⟨m, hm⟩ := hEven
    obtain ⟨k, hk⟩ := hSeven
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.1 hdiff
  obtain ⟨huN, huS⟩ := mem_sdiff.1 hu
  obtain ⟨hvN, hvS⟩ := mem_sdiff.1 hv
  -- every neighbour of an unmatched vertex is matched
  have hnbhd : ∀ y ∈ N, y ∉ S → nbhdOn A N y ⊆ S := by
    intro y hyN hyS x hx
    by_contra hxS
    obtain ⟨hxy, hxN, -⟩ := mem_nbhdOn.1 hx
    exact hbig y x _ hyS hxS hxy.symm hyN hxN
      (isMatchingOn_insert_insert hf hyS hxS hxy.symm hx hyN)
  -- no matched edge has one end adjacent to `u` and the other adjacent to `v`
  have hcross : ∀ x ∈ nbhdOn A N u, f x ∉ nbhdOn A N v := by
    intro x hx hfx
    exact hbig u v _ huS hvS huv huN hvN
      (isMatchingOn_augment hf huS hvS huv (hnbhd u huN huS hx) hx hfx huN hvN)
  -- hence `f` injects the neighbourhood of `u` into `S` away from the neighbourhood of `v`
  have hinj : Set.InjOn f (nbhdOn A N u) := by
    intro a ha b hb hab
    have ha' := hnbhd u huN huS ha
    have hb' := hnbhd u huN huS hb
    rw [← hf.invol a ha', ← hf.invol b hb', hab]
  have himg : (nbhdOn A N u).image f ⊆ S \ nbhdOn A N v := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact mem_sdiff.2 ⟨hf.mapsTo x (hnbhd u huN huS hx), hcross x hx⟩
  have hcards : (nbhdOn A N u).card + (nbhdOn A N v).card ≤ S.card := by
    have h1 : ((nbhdOn A N u).image f).card = (nbhdOn A N u).card := card_image_of_injOn hinj
    have h2 : ((nbhdOn A N u).image f).card + (nbhdOn A N v).card ≤ S.card := by
      have hsub : nbhdOn A N v ⊆ S := hnbhd v hvN hvS
      calc ((nbhdOn A N u).image f).card + (nbhdOn A N v).card
          = ((nbhdOn A N u).image f ∪ nbhdOn A N v).card := by
            rw [card_union_of_disjoint]
            exact Finset.disjoint_left.2 fun a ha hb => (mem_sdiff.1 (himg ha)).2 hb
        _ ≤ S.card := card_le_card (union_subset (himg.trans sdiff_subset) hsub)
    omega
  have h1 := hdeg u huN
  have h2 := hdeg v hvN
  obtain ⟨m, hm⟩ := hEven
  omega

/-- Monotonicity of neighbourhoods in the edge set. -/
private theorem nbhdOn_mono {A' : Finset (Sym2 V)} (h : A' ⊆ A) (v : V) :
    nbhdOn A' N v ⊆ nbhdOn A N v := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := mem_nbhdOn.1 hz
  exact mem_nbhdOn.2 ⟨h1, h2, h h3⟩

/-- A matching for a smaller edge set is a matching for a larger one. -/
private theorem IsMatchingOn.mono {A' : Finset (Sym2 V)} (hM : IsMatchingOn A' N S f)
    (h : A' ⊆ A) : IsMatchingOn A N S f :=
  ⟨hM.mapsTo, hM.invol, hM.ne, fun a ha => nbhdOn_mono h a (hM.adj a ha)⟩

/-- Deleting the edges of a partner involution removes exactly the partner from each
neighbourhood. -/
private theorem nbhdOn_sdiff_image (hM : IsMatchingOn A N N f) {y : V} (hy : y ∈ N) :
    nbhdOn (A \ N.image fun a => s(a, f a)) N y = (nbhdOn A N y).erase (f y) := by
  ext z
  simp only [mem_nbhdOn, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_image, not_exists]
  constructor
  · rintro ⟨hzy, hzN, hzA, hzI⟩
    refine ⟨?_, hzy, hzN, hzA⟩
    rintro rfl
    exact hzI y ⟨hy, rfl⟩
  · rintro ⟨hzf, hzy, hzN, hzA⟩
    refine ⟨hzy, hzN, hzA, ?_⟩
    rintro a ⟨ha, hae⟩
    rcases Sym2.eq_iff.1 hae with ⟨rfl, rfl⟩ | ⟨rfl, hfa⟩
    · exact hzf rfl
    · exact hzf (by rw [← hfa, hM.invol _ ha])

/-- Deleting the edges of a perfect matching of `N` drops every degree inside `N` by exactly
one. -/
private theorem card_nbhdOn_sdiff_image (hM : IsMatchingOn A N N f) {y : V} (hy : y ∈ N) :
    (nbhdOn (A \ N.image fun a => s(a, f a)) N y).card + 1 = (nbhdOn A N y).card := by
  rw [nbhdOn_sdiff_image hM hy, card_erase_of_mem (hM.adj y hy)]
  have : 0 < (nbhdOn A N y).card := card_pos.2 ⟨f y, hM.adj y hy⟩
  omega

/-- The inductive form of the spread bound: with Dirac slack `t`, some perfect matching of `N`
inside `A` has weight at most a `1 / (t + 1)` fraction of the total weight available in `A`. -/
private theorem exists_isMatchingOn_weight (hEven : Even N.card) (w : V → V → ℝ)
    (hw : ∀ y z, 0 ≤ w y z) :
    ∀ (t : ℕ) (A : Finset (Sym2 V)), (∀ v ∈ N, N.card / 2 + t ≤ (nbhdOn A N v).card) →
      ∃ f : V → V, IsMatchingOn A N N f ∧
        ((t : ℝ) + 1) * ∑ y ∈ N, w y (f y) ≤ ∑ y ∈ N, ∑ z ∈ nbhdOn A N y, w y z := by
  intro t
  induction t with
  | zero =>
    intro A hdeg
    obtain ⟨f, hf⟩ := exists_isMatchingOn (A := A) hEven fun v hv => by have := hdeg v hv; omega
    refine ⟨f, hf, ?_⟩
    rw [Nat.cast_zero, zero_add, one_mul]
    exact Finset.sum_le_sum fun y hy =>
      Finset.single_le_sum (f := fun z => w y z) (fun z _ => hw y z) (hf.adj y hy)
  | succ t ih =>
    intro A hdeg
    obtain ⟨f₀, hf₀⟩ := exists_isMatchingOn (A := A) hEven fun v hv => by
      have := hdeg v hv; omega
    set A' := A \ N.image fun a => s(a, f₀ a) with hA'
    have hdeg' : ∀ v ∈ N, N.card / 2 + t ≤ (nbhdOn A' N v).card := by
      intro v hv
      have h1 := hdeg v hv
      have h2 := card_nbhdOn_sdiff_image hf₀ hv
      rw [hA']
      omega
    obtain ⟨f₁, hf₁, hb₁⟩ := ih A' hdeg'
    have hsplit : ∑ y ∈ N, ∑ z ∈ nbhdOn A' N y, w y z
        = (∑ y ∈ N, ∑ z ∈ nbhdOn A N y, w y z) - ∑ y ∈ N, w y (f₀ y) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [nbhdOn_sdiff_image hf₀ hy, Finset.sum_erase_eq_sub (hf₀.adj y hy)]
    rw [hsplit] at hb₁
    have htpos : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
    by_cases hcmp : ∑ y ∈ N, w y (f₀ y) ≤ ∑ y ∈ N, w y (f₁ y)
    · refine ⟨f₀, hf₀, ?_⟩
      have h5 := mul_le_mul_of_nonneg_left hcmp htpos
      push_cast
      linarith
    · push Not at hcmp
      refine ⟨f₁, hf₁.mono sdiff_subset, ?_⟩
      push_cast
      linarith

/-- The inductive form of the edge-disjointness statement: with Dirac slack `t` there are `t + 1`
pairwise edge-disjoint perfect matchings of `N` inside `A`. -/
private theorem exists_isMatchingOn_pairwise (hEven : Even N.card) :
    ∀ (t : ℕ) (A : Finset (Sym2 V)), (∀ v ∈ N, N.card / 2 + t ≤ (nbhdOn A N v).card) →
      ∃ F : Fin (t + 1) → V → V, (∀ i, IsMatchingOn A N N (F i)) ∧
        ∀ i j, i ≠ j → ∀ a ∈ N, F i a ≠ F j a := by
  intro t
  induction t with
  | zero =>
    intro A hdeg
    obtain ⟨f, hf⟩ := exists_isMatchingOn (A := A) hEven fun v hv => by have := hdeg v hv; omega
    refine ⟨fun _ => f, fun _ => hf, fun i j hij => ?_⟩
    have hi := i.isLt
    have hj := j.isLt
    exact absurd (Fin.val_injective (by omega : (i : ℕ) = j)) hij
  | succ t ih =>
    intro A hdeg
    obtain ⟨f₀, hf₀⟩ := exists_isMatchingOn (A := A) hEven fun v hv => by
      have := hdeg v hv; omega
    set A' := A \ N.image fun a => s(a, f₀ a) with hA'
    have hdeg' : ∀ v ∈ N, N.card / 2 + t ≤ (nbhdOn A' N v).card := by
      intro v hv
      have h1 := hdeg v hv
      have h2 := card_nbhdOn_sdiff_image hf₀ hv
      rw [hA']
      omega
    obtain ⟨F', hF', hne'⟩ := ih A' hdeg'
    have hnew : ∀ i, ∀ a ∈ N, F' i a ≠ f₀ a := by
      intro i a ha h
      have hmem := (mem_nbhdOn.1 ((hF' i).adj a ha)).2.2
      rw [h] at hmem
      exact (Finset.mem_sdiff.1 hmem).2 (Finset.mem_image.2 ⟨a, ha, rfl⟩)
    refine ⟨Fin.cons f₀ F', ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · simpa using hf₀
      · intro i
        simpa using (hF' i).mono sdiff_subset
    · refine Fin.cases (fun j => ?_) (fun i j => ?_)
      · refine Fin.cases (fun h => absurd rfl h) (fun j _ a ha => ?_) j
        simpa using (hnew j a ha).symm
      · refine Fin.cases (fun _ a ha => ?_) (fun j hij a ha => ?_) j
        · simpa using hnew i a ha
        · have hij' : i ≠ j := fun h => hij (by rw [h])
          simpa using hne' i j hij' a ha

end Aux

/-! ### Dirac's theorem and spread matchings for simple graphs -/

variable {G : SimpleGraph V} [DecidableRel G.Adj] {N : Finset V} {t : ℕ}

open scoped Classical in
/-- The neighbourhoods used in the auxiliary development are the graph neighbourhoods
inside `N`. -/
private theorem nbhdOn_graph {v : V} (hv : v ∈ N) :
    nbhdOn (N.sym2.filter fun e => e ∈ G.edgeSet) N v = N.filter fun z => G.Adj v z := by
  ext z
  rw [mem_nbhdOn, mem_filter, mem_filter]
  constructor
  · rintro ⟨-, hzN, -, hA⟩
    exact ⟨hzN, by simpa using hA⟩
  · rintro ⟨hzN, hadj⟩
    refine ⟨hadj.ne', hzN, ?_, by simpa using hadj⟩
    rw [Finset.mem_sym2_iff]
    intro y hy
    rcases Sym2.mem_iff.1 hy with rfl | rfl
    · exact hv
    · exact hzN

omit [DecidableEq V] in
/-- **Dirac's theorem for perfect matchings.**  If `N` is a finite set of vertices of even
cardinality such that every `v ∈ N` has at least `|N| / 2` neighbours inside `N`, then `N` carries
a perfect matching of `G`, presented as a fixed-point-free partner involution `f` of `N` with
`G.Adj a (f a)` for all `a ∈ N`. -/
theorem exists_involution_adj (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 ≤ (N.filter fun z => G.Adj v z).card) :
    ∃ f : V → V, (∀ a ∈ N, f a ∈ N) ∧ (∀ a ∈ N, f (f a) = a) ∧ (∀ a ∈ N, f a ≠ a) ∧
      ∀ a ∈ N, G.Adj a (f a) := by
  classical
  obtain ⟨f, hf⟩ :=
    exists_isMatchingOn (A := N.sym2.filter fun e => e ∈ G.edgeSet) hEven fun v hv => by
      rw [nbhdOn_graph hv]; exact hdeg v hv
  refine ⟨f, hf.mapsTo, hf.invol, hf.ne, fun a ha => ?_⟩
  have := (mem_filter.1 (mem_nbhdOn.1 (hf.adj a ha)).2.2).2
  simpa using this

omit [DecidableEq V] in
/-- **Dirac's theorem with slack.**  If every vertex of an even set `N` has at least `|N| / 2 + t`
neighbours inside `N`, then `G` contains `t + 1` perfect matchings of `N` which are pairwise
edge-disjoint: distinct matchings assign distinct partners to every vertex of `N`. -/
theorem exists_involutions_pairwise_ne (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card) :
    ∃ F : Fin (t + 1) → V → V, (∀ i, (∀ a ∈ N, F i a ∈ N) ∧ (∀ a ∈ N, F i (F i a) = a) ∧
        (∀ a ∈ N, F i a ≠ a) ∧ ∀ a ∈ N, G.Adj a (F i a)) ∧
      ∀ i j, i ≠ j → ∀ a ∈ N, F i a ≠ F j a := by
  classical
  obtain ⟨F, hF, hne⟩ :=
    exists_isMatchingOn_pairwise (A := N.sym2.filter fun e => e ∈ G.edgeSet) hEven t fun v hv => by
      rw [nbhdOn_graph hv]; exact hdeg v hv
  refine ⟨F, fun i => ⟨(hF i).mapsTo, (hF i).invol, (hF i).ne, fun a ha => ?_⟩, hne⟩
  have := (mem_filter.1 (mem_nbhdOn.1 ((hF i).adj a ha)).2.2).2
  simpa using this

omit [DecidableEq V] in
/-- **Spread perfect matchings from Dirac slack.**  If every vertex of an even set `N` has at least
`|N| / 2 + t` neighbours inside `N`, then for every nonnegative weight function `w` some perfect
matching of `N`, presented as a partner involution `f`, has weight at most a `1 / (t + 1)` fraction
of the total weight: `∑ y ∈ N, w y (f y) ≤ (1 / (t + 1)) * ∑ y ∈ N, ∑ z ∈ N, w y z`.

The matching is obtained by averaging over the `t + 1` pairwise edge-disjoint perfect matchings
supplied by `SimpleGraph.exists_involutions_pairwise_ne`. -/
theorem exists_spread_involution (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    (w : V → V → ℝ) (hw : ∀ y z, 0 ≤ w y z) :
    ∃ f : V → V, (∀ a ∈ N, f a ∈ N) ∧ (∀ a ∈ N, f (f a) = a) ∧ (∀ a ∈ N, f a ≠ a) ∧
      (∀ a ∈ N, G.Adj a (f a)) ∧
      ∑ y ∈ N, w y (f y) ≤ (1 / ((t : ℝ) + 1)) * ∑ y ∈ N, ∑ z ∈ N, w y z := by
  classical
  set A : Finset (Sym2 V) := N.sym2.filter fun e => e ∈ G.edgeSet with hA
  obtain ⟨f, hf, hbound⟩ :=
    exists_isMatchingOn_weight (N := N) hEven w hw t A fun v hv => by
      rw [hA, nbhdOn_graph hv]; exact hdeg v hv
  refine ⟨f, hf.mapsTo, hf.invol, hf.ne, fun a ha => ?_, ?_⟩
  · have := (mem_filter.1 (mem_nbhdOn.1 (hf.adj a ha)).2.2).2
    simpa using this
  · have hmono : ∑ y ∈ N, ∑ z ∈ nbhdOn A N y, w y z ≤ ∑ y ∈ N, ∑ z ∈ N, w y z :=
      Finset.sum_le_sum fun y _ =>
        Finset.sum_le_sum_of_subset_of_nonneg nbhdOn_subset fun z _ _ => hw y z
    have hkey : ((t : ℝ) + 1) * ∑ y ∈ N, w y (f y) ≤ ∑ y ∈ N, ∑ z ∈ N, w y z := hbound.trans hmono
    have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    rw [show (1 / ((t : ℝ) + 1)) * ∑ y ∈ N, ∑ z ∈ N, w y z
        = (∑ y ∈ N, ∑ z ∈ N, w y z) / ((t : ℝ) + 1) by ring, le_div_iff₀ hpos]
    linarith

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A fixed-point-free involution all of whose orbits are edges of `G` is a perfect matching
of `G`, in the sense of `SimpleGraph.Subgraph.IsPerfectMatching`. -/
theorem exists_isPerfectMatching_of_involutive {f : V → V} (hinv : ∀ a, f (f a) = a)
    (hadj : ∀ a, G.Adj a (f a)) : ∃ M : G.Subgraph, M.IsPerfectMatching ∧ ∀ a, M.Adj a (f a) := by
  refine ⟨{ verts := Set.univ
            Adj := fun a b => G.Adj a b ∧ f a = b
            adj_sub := fun h => h.1
            edge_vert := fun _ => trivial
            symm := ⟨fun a b h => ⟨h.1.symm, by rw [← h.2, hinv]⟩⟩ },
    ?_, fun a => ⟨hadj a, rfl⟩⟩
  rw [Subgraph.isPerfectMatching_iff]
  exact fun v => ⟨f v, ⟨hadj v, rfl⟩, fun w hw => hw.2.symm⟩

omit [DecidableEq V] in
/-- **Dirac's theorem for perfect matchings**, for a finite graph with an even number of vertices
and minimum degree at least half the number of vertices. -/
theorem exists_isPerfectMatching_of_card_le_minDegree [Fintype V]
    (hEven : Even (Fintype.card V)) (hdeg : Fintype.card V / 2 ≤ G.minDegree) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨f, -, hinv, -, hadj⟩ :=
    exists_involution_adj (G := G) (N := Finset.univ) (by simpa using hEven) fun v _ => by
      have h1 : (Finset.univ.filter fun z => G.Adj v z) = G.neighborFinset v := by
        ext z; simp
      rw [h1, card_univ]
      exact le_trans hdeg (G.minDegree_le_degree v)
  obtain ⟨M, hM, -⟩ :=
    exists_isPerfectMatching_of_involutive (fun a => hinv a (mem_univ a))
      fun a => hadj a (mem_univ a)
  exact ⟨M, hM⟩

end SimpleGraph
