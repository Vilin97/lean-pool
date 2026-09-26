/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import LeanPool.OrderClosures.BanLat.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Set.Countable


/-!
# Sigma conditional completeness

Mathlib's `ConditionallyCompleteLattice` records Dedekind completeness of a
lattice. This file gives vector-lattice characterisations of conditional
completeness, introduces the sequential analogue
`SigmaConditionallyCompleteLattice`, and relates these completeness notions to
the Archimedean property.
-/

@[expose] public section

open Set

universe u

/-! ### Shared order-completeness lemmas -/

/-- Shift trick: in a lattice-ordered group, given a predicate `P` preserved
under pointwise transformations and a hypothesis producing a least upper bound
for `P`-sets of positive elements, the same hypothesis extends to any
`P`-set that is non-empty and bounded above. -/
lemma exists_isLUB_of_pos_of_shift
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    {P : Set X → Prop}
    (hP_image : ∀ {S : Set X} (f : X → X), P S → P (f '' S))
    (Hpos : ∀ {S : Set X}, P S → S ⊆ {x | 0 ≤ x} → S.Nonempty → BddAbove S →
      ∃ x, IsLUB S x)
    {S : Set X} (hPS : P S) (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ x, IsLUB S x := by
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨c, hc⟩ := hbdd
  have hcs₀ : s₀ ≤ c := hc hs₀
  set T : Set X := (fun x => (x - s₀)⁺) '' S with hT_def
  have hPT : P T := hP_image _ hPS
  have hTpos : T ⊆ {x | 0 ≤ x} := by
    rintro _ ⟨x, _, rfl⟩; exact posPart_nonneg _
  have hTne : T.Nonempty := ⟨_, s₀, hs₀, rfl⟩
  have hTbdd : BddAbove T := ⟨c - s₀, by
    rintro _ ⟨x, hx, rfl⟩
    calc (x - s₀)⁺ ≤ (c - s₀)⁺ := posPart_mono (sub_le_sub_right (hc hx) _)
      _ = c - s₀ := posPart_of_nonneg (sub_nonneg.mpr hcs₀)⟩
  obtain ⟨w, hw⟩ := Hpos hPT hTpos hTne hTbdd
  refine ⟨w + s₀, ?_, ?_⟩
  · intro x hx
    calc x = (x - s₀) + s₀ := by abel
      _ ≤ (x - s₀)⁺ + s₀ := by gcongr; exact le_posPart _
      _ ≤ w + s₀ := by gcongr; exact hw.1 ⟨x, hx, rfl⟩
  · intro c' hc'
    have hcs₀' : s₀ ≤ c' := hc' hs₀
    have hubT : c' - s₀ ∈ upperBounds T := by
      rintro _ ⟨x, hx, rfl⟩
      calc (x - s₀)⁺ ≤ (c' - s₀)⁺ := posPart_mono (sub_le_sub_right (hc' hx) _)
        _ = c' - s₀ := posPart_of_nonneg (sub_nonneg.mpr hcs₀')
    exact le_sub_iff_add_le.mp (hw.2 hubT)

/-- Build a `ConditionallyCompleteLattice` structure from a blanket hypothesis
that every non-empty bounded above set has a least upper bound. -/
@[reducible]
noncomputable def conditionallyCompleteLatticeOfHasLUB
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (hLUB : ∀ {S : Set X}, S.Nonempty → BddAbove S → ∃ x, IsLUB S x) :
    ConditionallyCompleteLattice X := by
  classical
  have hne_neg : ∀ (s : Set X), s.Nonempty → (-s).Nonempty := fun s hne => by
    obtain ⟨x, hx⟩ := hne
    exact ⟨-x, Set.mem_neg.mpr (by rwa [neg_neg])⟩
  let sSup_fn : Set X → X := fun S =>
    if h : S.Nonempty ∧ BddAbove S then Classical.choose (hLUB h.1 h.2) else 0
  exact
  { (inferInstance : Lattice X) with
    sSup := sSup_fn
    sInf := fun S => -sSup_fn (-S)
    isLUB_csSup := fun s hne hb => by
      refine ⟨?_, ?_⟩
      · intro a ha
        change a ≤ sSup_fn s
        simp only [sSup_fn, dite_eq_left (⟨hne, hb⟩ : s.Nonempty ∧ BddAbove s)]
        exact (Classical.choose_spec (hLUB hne hb)).1 ha
      · intro a ha
        change sSup_fn s ≤ a
        simp only [sSup_fn, dite_eq_left (⟨hne, ⟨a, ha⟩⟩ : s.Nonempty ∧ BddAbove s)]
        exact (Classical.choose_spec (hLUB hne ⟨a, ha⟩)).2 ha
    isGLB_csInf := fun s hne hb => by
      refine ⟨?_, ?_⟩
      · intro a ha
        change -sSup_fn (-s) ≤ a
        have hne' : (-s).Nonempty := hne_neg s hne
        have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hb
        simp only [sSup_fn, dite_eq_left (⟨hne', hbdd'⟩ : (-s).Nonempty ∧ BddAbove (-s))]
        rw [neg_le]
        exact (Classical.choose_spec (hLUB hne' hbdd')).1
          (Set.mem_neg.mpr (by rwa [neg_neg]))
      · intro a ha
        change a ≤ -sSup_fn (-s)
        have hb' : BddBelow s := ⟨a, ha⟩
        have hne' : (-s).Nonempty := hne_neg s hne
        have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hb'
        simp only [sSup_fn, dite_eq_left (⟨hne', hbdd'⟩ : (-s).Nonempty ∧ BddAbove (-s))]
        rw [le_neg]
        apply (Classical.choose_spec (hLUB hne' hbdd')).2
        intro y hy
        rw [Set.mem_neg] at hy
        rw [le_neg]
        exact ha hy }

/-- From the existence of a least upper bound for every increasing bounded
above net of positive elements, deduce the same conclusion for any non-empty
bounded above set of positive elements. The net is obtained by indexing over
non-empty finite subsets ordered by inclusion. -/
lemma exists_isLUB_pos_set_of_pos_net
    {X : Type u} [AddCommGroup X] [Lattice X]
    (H : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
        {u : ι → X}, Monotone u → (∀ i, 0 ≤ u i) →
        BddAbove (range u) → ∃ x, IsLUB (range u) x)
    {S : Set X} (hpos : S ⊆ {x | 0 ≤ x}) (hne : S.Nonempty)
    (hbdd : BddAbove S) : ∃ x, IsLUB S x := by
  classical
  let ι : Type u := {F : Finset X // F.Nonempty ∧ ↑F ⊆ S}
  let : Preorder ι := inferInstance
  let : IsDirected ι (· ≤ ·) := ⟨fun F G =>
    ⟨⟨F.1 ∪ G.1, Finset.Nonempty.mono Finset.subset_union_left F.2.1, by
      rw [Finset.coe_union]; exact Set.union_subset F.2.2 G.2.2⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩⟩
  let : Nonempty ι := by
    obtain ⟨s₀, hs₀⟩ := hne
    exact ⟨⟨{s₀}, Finset.singleton_nonempty _, by simpa using hs₀⟩⟩
  let u : ι → X := fun F => F.1.sup' F.2.1 id
  have hmono : Monotone u := fun F G h =>
    Finset.sup'_mono id h F.2.1
  have hu_pos : ∀ F, 0 ≤ u F := fun F => by
    obtain ⟨x, hx⟩ := F.2.1
    calc (0 : X) ≤ x := hpos (F.2.2 hx)
      _ ≤ u F := Finset.le_sup' id hx
  have hu_bdd : BddAbove (range u) := by
    obtain ⟨c, hc⟩ := hbdd
    refine ⟨c, ?_⟩
    rintro _ ⟨F, rfl⟩
    refine Finset.sup'_le F.2.1 id fun i hi => hc (F.2.2 ?_)
    exact Finset.mem_coe.mpr hi
  obtain ⟨w, hw⟩ := H hmono hu_pos hu_bdd
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    have hmem : u ⟨{x}, Finset.singleton_nonempty _, by simpa using hx⟩ = x := by
      simp [u, Finset.sup'_singleton]
    calc x = u ⟨{x}, Finset.singleton_nonempty _, by simpa using hx⟩ := hmem.symm
      _ ≤ w := hw.1 ⟨_, rfl⟩
  · intro c hc
    apply hw.2
    rintro _ ⟨F, rfl⟩
    refine Finset.sup'_le F.2.1 id fun i hi => hc (F.2.2 ?_)
    exact Finset.mem_coe.mpr hi

/-! ### Characterisations of `ConditionallyCompleteLattice` -/

/-- On a lattice-ordered additive commutative group, a
`ConditionallyCompleteLattice` structure exists provided every increasing net
of positive elements that is bounded above has a least upper bound. The net is
indexed by a type in the same universe as the carrier. -/
@[reducible]
noncomputable def conditionallyCompleteLatticeOfPosNet
    (X : Type u) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (H : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
        {u : ι → X}, Monotone u → (∀ i, 0 ≤ u i) →
        BddAbove (range u) → ∃ x, IsLUB (range u) x) :
    ConditionallyCompleteLattice X :=
  conditionallyCompleteLatticeOfHasLUB
    (exists_isLUB_of_pos_of_shift (P := fun _ => True)
      (fun _ _ => trivial)
      (fun _ hpos hne hbdd => exists_isLUB_pos_set_of_pos_net H hpos hne hbdd)
      trivial)

/-- On a lattice-ordered additive commutative group, a
`ConditionallyCompleteLattice` structure exists provided every non-empty
bounded above set of positive elements has a least upper bound. -/
@[reducible]
noncomputable def conditionallyCompleteLatticeOfPosSet
    (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (H : ∀ {S : Set X}, S ⊆ {x | 0 ≤ x} → S.Nonempty → BddAbove S →
      ∃ x, IsLUB S x) :
    ConditionallyCompleteLattice X :=
  conditionallyCompleteLatticeOfHasLUB
    (exists_isLUB_of_pos_of_shift (P := fun _ => True)
      (fun _ _ => trivial) (fun _ hpos hne hbdd => H hpos hne hbdd) trivial)

/-! ### Sigma conditional completeness -/

/-- A lattice is **sigma conditionally complete** when non-empty bounded
countable subsets admit suprema and infima: for every countable set `s`,
`sSup s` is the least upper bound if `s` is bounded above, and `sInf s` is
the greatest lower bound if `s` is bounded below. -/
class SigmaConditionallyCompleteLattice (X : Type*)
    extends Lattice X, SupSet X, InfSet X where
  le_csSup : ∀ (s : Set X) (a : X), s.Countable → BddAbove s → a ∈ s → a ≤ sSup s
  csSup_le : ∀ (s : Set X) (a : X), s.Countable → s.Nonempty →
    a ∈ upperBounds s → sSup s ≤ a
  csInf_le : ∀ (s : Set X) (a : X), s.Countable → BddBelow s → a ∈ s → sInf s ≤ a
  le_csInf : ∀ (s : Set X) (a : X), s.Countable → s.Nonempty →
    a ∈ lowerBounds s → a ≤ sInf s

/-- Every conditionally complete lattice is sigma conditionally complete. -/
instance (priority := 100) ConditionallyCompleteLattice.toSigmaConditionallyCompleteLattice
    {X : Type*} [ConditionallyCompleteLattice X] :
    SigmaConditionallyCompleteLattice X where
  le_csSup _ _ _ hb ha := _root_.le_csSup hb ha
  csSup_le _ _ _ hne ha := _root_.csSup_le hne ha
  csInf_le _ _ _ hb ha := _root_.csInf_le hb ha
  le_csInf _ _ _ hne ha := _root_.le_csInf hne ha

/-! ### Characterisations of sigma conditional completeness -/

/-- Build a `SigmaConditionallyCompleteLattice` structure from a hypothesis
that every countable non-empty bounded above set has a least upper bound. -/
@[reducible]
noncomputable def sigmaConditionallyCompleteLatticeOfHasCountableLUB
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (hLUB : ∀ {S : Set X}, S.Countable → S.Nonempty → BddAbove S →
      ∃ x, IsLUB S x) :
    SigmaConditionallyCompleteLattice X := by
  classical
  have hne_neg : ∀ (s : Set X), s.Nonempty → (-s).Nonempty := fun s hne => by
    obtain ⟨x, hx⟩ := hne
    exact ⟨-x, Set.mem_neg.mpr (by rwa [neg_neg])⟩
  have hcount_neg : ∀ (s : Set X), s.Countable → (-s).Countable := fun s hc => by
    have : -s = (fun x => -x) '' s := by ext; simp [Set.mem_neg]
    rw [this]; exact hc.image _
  let sSup_fn : Set X → X := fun S =>
    if h : S.Countable ∧ S.Nonempty ∧ BddAbove S
    then Classical.choose (hLUB h.1 h.2.1 h.2.2) else 0
  exact
  { (inferInstance : Lattice X) with
    sSup := sSup_fn
    sInf := fun S => -sSup_fn (-S)
    le_csSup := fun s a hc hb ha => by
      have hne : s.Nonempty := ⟨a, ha⟩
      change a ≤ sSup_fn s
      simp only [sSup_fn,
        dite_eq_left (⟨hc, hne, hb⟩ : s.Countable ∧ s.Nonempty ∧ BddAbove s)]
      exact (Classical.choose_spec (hLUB hc hne hb)).1 ha
    csSup_le := fun s a hc hne ha => by
      have hb : BddAbove s := ⟨a, ha⟩
      change sSup_fn s ≤ a
      simp only [sSup_fn,
        dite_eq_left (⟨hc, hne, hb⟩ : s.Countable ∧ s.Nonempty ∧ BddAbove s)]
      exact (Classical.choose_spec (hLUB hc hne hb)).2 ha
    csInf_le := fun s a hc hb ha => by
      change -sSup_fn (-s) ≤ a
      have hc' : (-s).Countable := hcount_neg s hc
      have hne' : (-s).Nonempty := hne_neg s ⟨a, ha⟩
      have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hb
      simp only [sSup_fn,
        dite_eq_left (⟨hc', hne', hbdd'⟩ : (-s).Countable ∧ (-s).Nonempty ∧ BddAbove (-s))]
      rw [neg_le]
      exact (Classical.choose_spec (hLUB hc' hne' hbdd')).1
        (Set.mem_neg.mpr (by rwa [neg_neg]))
    le_csInf := fun s a hc hne ha => by
      change a ≤ -sSup_fn (-s)
      have hb : BddBelow s := ⟨a, ha⟩
      have hc' : (-s).Countable := hcount_neg s hc
      have hne' : (-s).Nonempty := hne_neg s hne
      have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hb
      simp only [sSup_fn,
        dite_eq_left (⟨hc', hne', hbdd'⟩ : (-s).Countable ∧ (-s).Nonempty ∧ BddAbove (-s))]
      rw [le_neg]
      apply (Classical.choose_spec (hLUB hc' hne' hbdd')).2
      intro y hy
      rw [Set.mem_neg] at hy
      rw [le_neg]
      exact ha hy }

/-- From the existence of a least upper bound for every increasing bounded
above sequence of positive elements, deduce the same conclusion for every
non-empty bounded above countable set of positive elements. The sequence is
obtained by enumerating the set and taking finite suprema. -/
lemma exists_isLUB_pos_countable_set_of_pos_seq
    {X : Type*} [AddCommGroup X] [Lattice X]
    (H : ∀ {u : ℕ → X}, Monotone u → (∀ n, 0 ≤ u n) →
      BddAbove (range u) → ∃ x, IsLUB (range u) x)
    {S : Set X} (hpos : S ⊆ {x | 0 ≤ x}) (hcount : S.Countable)
    (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x, IsLUB S x := by
  classical
  obtain ⟨g, hg⟩ := hcount.exists_eq_range hne
  let u : ℕ → X := fun n =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one g
  have hg_pos : ∀ i, 0 ≤ g i := fun i => hpos (hg ▸ mem_range_self i)
  have hg_le : ∀ i c, c ∈ upperBounds S → g i ≤ c := fun i c hc =>
    hc (hg ▸ mem_range_self i)
  have hmono : Monotone u := fun m n hmn =>
    Finset.sup'_mono g (Finset.range_subset_range.mpr (Nat.succ_le_succ hmn))
      Finset.nonempty_range_add_one
  have hu_pos : ∀ n, 0 ≤ u n := fun n => by
    calc (0 : X) ≤ g 0 := hg_pos 0
      _ ≤ u n := Finset.le_sup' g (Finset.mem_range.mpr (Nat.succ_pos n))
  have hu_bdd : BddAbove (range u) := by
    obtain ⟨c, hc⟩ := hbdd
    refine ⟨c, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Finset.sup'_le _ _ fun i _ => hg_le i c hc
  obtain ⟨w, hw⟩ := H hmono hu_pos hu_bdd
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    rw [hg] at hx
    obtain ⟨n, rfl⟩ := hx
    exact (Finset.le_sup' g (Finset.self_mem_range_succ n)).trans (hw.1 ⟨n, rfl⟩)
  · intro c hc
    apply hw.2
    rintro _ ⟨n, rfl⟩
    exact Finset.sup'_le _ _ fun i _ => hg_le i c hc

/-- On a lattice-ordered additive commutative group, a `SigmaConditionallyCompleteLattice` structure
exists provided every increasing bounded above sequence of positive elements
has a least upper bound. -/
@[reducible]
noncomputable def sigmaConditionallyCompleteLatticeOfPosSeq
    (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (H : ∀ {u : ℕ → X}, Monotone u → (∀ n, 0 ≤ u n) →
      BddAbove (range u) → ∃ x, IsLUB (range u) x) :
    SigmaConditionallyCompleteLattice X :=
  sigmaConditionallyCompleteLatticeOfHasCountableLUB
    (exists_isLUB_of_pos_of_shift (P := Set.Countable)
      (fun f hc => hc.image f)
      (fun hc hpos hne hbdd =>
        exists_isLUB_pos_countable_set_of_pos_seq H hpos hc hne hbdd))

/-- On a lattice-ordered additive commutative group, a `SigmaConditionallyCompleteLattice` structure
exists provided every non-empty bounded above countable set of positive
elements has a least upper bound. -/
@[reducible]
noncomputable def sigmaConditionallyCompleteLatticeOfPosCountableSet
    (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (H : ∀ {S : Set X}, S ⊆ {x | 0 ≤ x} → S.Countable → S.Nonempty →
      BddAbove S → ∃ x, IsLUB S x) :
    SigmaConditionallyCompleteLattice X :=
  sigmaConditionallyCompleteLatticeOfHasCountableLUB
    (exists_isLUB_of_pos_of_shift (P := Set.Countable)
      (fun f hc => hc.image f)
      (fun hc hpos hne hbdd => H hpos hc hne hbdd))

/-! ### Archimedean property -/

/-- Every sigma conditionally complete lattice-ordered group is Archimedean
in the vector-lattice sense. -/
theorem IsVLArchimedean_of_sigmaConditionallyCompleteLattice
    {X : Type*} [SigmaConditionallyCompleteLattice X] [AddCommGroup X]
    [IsOrderedAddMonoid X] : IsVLArchimedean X := by
  apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
  intro x y hx hn
  set S : Set X := Set.range (fun n : ℕ => n • x) with hS_def
  have hS_count : S.Countable := Set.countable_range _
  have hS_ne : S.Nonempty := ⟨0 • x, 0, rfl⟩
  have hS_bdd : BddAbove S := ⟨y, by rintro _ ⟨n, rfl⟩; exact hn n⟩
  set u := sSup S with hu_def
  have hm : ∀ m : ℕ, m • x ≤ u := fun m =>
    SigmaConditionallyCompleteLattice.le_csSup S _ hS_count hS_bdd ⟨m, rfl⟩
  have hub : u - x ∈ upperBounds S := by
    rintro _ ⟨m, rfl⟩
    rw [le_sub_iff_add_le, ← succ_nsmul]
    exact hm (m + 1)
  have hu' : u ≤ u - x :=
    SigmaConditionallyCompleteLattice.csSup_le S _ hS_count hS_ne hub
  have hx_nonpos : x ≤ 0 := by
    have h : u + x ≤ u := le_sub_iff_add_le.mp hu'
    have h' : u + x ≤ u + 0 := by rwa [add_zero]
    exact (add_le_add_iff_left u).mp h'
  exact le_antisymm hx_nonpos hx
