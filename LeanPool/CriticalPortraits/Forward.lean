/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/

import LeanPool.CriticalPortraits.Core
import LeanPool.CriticalPortraits.Portraits

/-!
# Forward bound (brick 3b): `T P` is level-canonical, for every degree `d`.

The crux geometric half of the Reconstruction Lemma: the delete-min survivors `T P` of a
critical portrait are always level-canonical, `∀ j < d, #{u ∈ T P : level u ≤ j} ≤ j`.
This is the global non-crossing/ballot "Catalan heart" of the general census proof, here
proved for ALL `d` (sorry-free, native_decide-free; axioms ⊆ {propext, Classical.choice,
Quot.sound}). Follows the paper proof `docs/b2_forward_reconstruction_2026-06-16.md`
(Lemma A laminar, Lemma B monotone columns, the Kernel, the laminar-forest recursion);
probe `probes/check_b2_forward.py` confirms `d ≤ 6`.

The proof has two parts.

* **PART I (`AbstractLaminar`)** — a self-contained combinatorial result about a finite
  family of half-open integer intervals `(lo e, hi e]` with columns `col e`, pairwise
  laminar (Lemma A), interval-injective, with the Lemma-B column monotonicities
  (`bRight`/`bLeft`/`bSeam`). The master bound `N(a,b) ≤ b - a` packages the Kernel
  (`g(e) ≤ h(e) - 1`), the laminar-forest recursion, and the no-tiling crux
  (a column scan `c* < q₁ ≤ ⋯ ≤ qₖ < c*`).

* **PART II (`CriticalPortraits`)** — the geometric edge model. Edges ARE the survivors:
  each survivor
  `x ∈ T P` is the top of a unique edge whose other endpoint is its immediate predecessor
  `predIn x` in its host critical set. `hi x = level x`, `col x = fiber x`,
  `lo x = level (predIn x)`. Lemmas A/B + interval-injectivity all reduce to ONE master
  non-alternation lemma `no_alt` (no two survivors' endpoints alternate `px < py < x < y`),
  which dispatches cross-host via the portrait's `Unlinked` clause and same-host via
  predecessor immediacy. Assembling the `Family` and applying the master bound at window
  `(0, j]` gives `T_levelCanonical`.
-/

/-! # PART I — Abstract laminar interval family: Kernel + forest recursion.

A finite family `E : Finset ι` of half-open integer intervals `(lo e, hi e]` with columns
`col e`, pairwise laminar (Lemma A), intervals identifying edges (`inj`), and the Lemma-B
column properties (`bRight`/`bLeft`/`bSeam`). The master bound
`N(a,b) := #{e ∈ E : a ≤ lo e ∧ hi e ≤ b} ≤ b - a` packages the Kernel + the
laminar-forest recursion + the no-tiling crux. -/

namespace AbstractLaminar

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- An abstract laminar family: an index set with low/high endpoints and a column. -/
structure Family (ι : Type*) [DecidableEq ι] where
  /-- The carrier index set of the family. -/
  E : Finset ι
  /-- The low endpoint of each index. -/
  lo : ι → ℕ
  /-- The high endpoint of each index. -/
  hi : ι → ℕ
  /-- The column of each index. -/
  col : ι → ℕ
  lh : ∀ e ∈ E, lo e < hi e
  inj : ∀ e ∈ E, ∀ f ∈ E, lo e = lo f → hi e = hi f → e = f
  laminar : ∀ e ∈ E, ∀ f ∈ E, ¬ (lo e < lo f ∧ lo f < hi e ∧ hi e < hi f)
  bRight : ∀ e ∈ E, ∀ f ∈ E, hi e = hi f → lo e < lo f → col f < col e
  bLeft : ∀ e ∈ E, ∀ f ∈ E, lo e = lo f → hi f < hi e → col e < col f
  bSeam : ∀ e ∈ E, ∀ f ∈ E, hi e = lo f → col e ≤ col f

variable (fam : Family ι)

/-- Edges contained in the window `(a, b]`. -/
def contained (a b : ℕ) : Finset ι :=
  fam.E.filter (fun e => a ≤ fam.lo e ∧ fam.hi e ≤ b)

/-- The count `N(a,b)`. -/
def N (a b : ℕ) : ℕ := (contained fam a b).card

lemma mem_contained {a b : ℕ} {e : ι} :
    e ∈ contained fam a b ↔ e ∈ fam.E ∧ a ≤ fam.lo e ∧ fam.hi e ≤ b := by
  unfold contained; rw [mem_filter]

/-- Empty window: no contained edges. -/
lemma N_eq_zero_of_le {a b : ℕ} (hba : b ≤ a) : N fam a b = 0 := by
  unfold N contained
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  rintro ⟨ha, hb⟩
  have := fam.lh e he
  omega

/-- Two overlapping edges are nested (laminarity). -/
lemma overlap_imp_nested {e f : ι} (he : e ∈ fam.E) (hf : f ∈ fam.E)
    (h1 : fam.lo e < fam.hi f) (h2 : fam.lo f < fam.hi e) :
    (fam.lo f ≤ fam.lo e ∧ fam.hi e ≤ fam.hi f) ∨
    (fam.lo e ≤ fam.lo f ∧ fam.hi f ≤ fam.hi e) := by
  have lam1 := fam.laminar e he f hf
  have lam2 := fam.laminar f hf e he
  omega

/-- "strict": interval not exactly the window. -/
def IsStrict (a b : ℕ) (e : ι) : Prop := fam.lo e ≠ a ∨ fam.hi e ≠ b

instance (a b : ℕ) (e : ι) : Decidable (IsStrict fam a b e) := by unfold IsStrict; infer_instance

/-- The strictly-contained indices of `fam` on the window `[a, b]`. -/
def Sstrict (a b : ℕ) : Finset ι := (contained fam a b).filter (IsStrict fam a b)

lemma mem_Sstrict {a b : ℕ} {e : ι} :
    e ∈ Sstrict fam a b ↔ (e ∈ fam.E ∧ a ≤ fam.lo e ∧ fam.hi e ≤ b) ∧
      (fam.lo e ≠ a ∨ fam.hi e ≠ b) := by
  unfold Sstrict IsStrict; rw [mem_filter, mem_contained]

/-- Strict edges containing `f`. -/
def containersS (a b : ℕ) (f : ι) : Finset ι :=
  (Sstrict fam a b).filter (fun g => fam.lo g ≤ fam.lo f ∧ fam.hi f ≤ fam.hi g)

lemma mem_containersS {a b : ℕ} {f g : ι} :
    g ∈ containersS fam a b f ↔
      ((g ∈ fam.E ∧ a ≤ fam.lo g ∧ fam.hi g ≤ b) ∧ (fam.lo g ≠ a ∨ fam.hi g ≠ b)) ∧
        fam.lo g ≤ fam.lo f ∧ fam.hi f ≤ fam.hi g := by
  unfold containersS; rw [mem_filter, mem_Sstrict]

lemma containersS_nonempty {a b : ℕ} {f : ι} (hf : f ∈ Sstrict fam a b) :
    (containersS fam a b f).Nonempty := by
  refine ⟨f, ?_⟩
  rw [mem_containersS]
  rw [mem_Sstrict] at hf
  exact ⟨hf, le_refl _, le_refl _⟩

open Classical in
/-- The strict root of `f`: widest strict containing edge (total; junk = `f` off `Sstrict`). -/
noncomputable def rootS (a b : ℕ) (f : ι) : ι :=
  if hf : f ∈ Sstrict fam a b then
    (Finset.exists_max_image (containersS fam a b f) (fun g => fam.hi g - fam.lo g)
      (containersS_nonempty fam hf)).choose
  else f

lemma rootS_mem_containersS {a b : ℕ} {f : ι} (hf : f ∈ Sstrict fam a b) :
    rootS fam a b f ∈ containersS fam a b f := by
  unfold rootS; rw [dif_pos hf]
  exact (Finset.exists_max_image (containersS fam a b f) (fun g => fam.hi g - fam.lo g)
    (containersS_nonempty fam hf)).choose_spec.1

lemma rootS_max {a b : ℕ} {f : ι} (hf : f ∈ Sstrict fam a b) :
    ∀ g ∈ containersS fam a b f,
      fam.hi g - fam.lo g ≤ fam.hi (rootS fam a b f) - fam.lo (rootS fam a b f) := by
  unfold rootS; rw [dif_pos hf]
  exact (Finset.exists_max_image (containersS fam a b f) (fun g => fam.hi g - fam.lo g)
    (containersS_nonempty fam hf)).choose_spec.2

variable {a b : ℕ}

lemma rootS_mem_E {f : ι} (hf : f ∈ Sstrict fam a b) : rootS fam a b f ∈ fam.E := by
  have := rootS_mem_containersS fam hf; rw [mem_containersS] at this; exact this.1.1.1

lemma rootS_mem_Sstrict {f : ι} (hf : f ∈ Sstrict fam a b) : rootS fam a b f ∈ Sstrict fam a b := by
  have := rootS_mem_containersS fam hf; rw [mem_containersS] at this
  rw [mem_Sstrict]; exact this.1

lemma rootS_window {f : ι} (hf : f ∈ Sstrict fam a b) :
    a ≤ fam.lo (rootS fam a b f) ∧ fam.hi (rootS fam a b f) ≤ b := by
  have := rootS_mem_containersS fam hf; rw [mem_containersS] at this; exact this.1.1.2

lemma rootS_strict {f : ι} (hf : f ∈ Sstrict fam a b) :
    fam.lo (rootS fam a b f) ≠ a ∨ fam.hi (rootS fam a b f) ≠ b := by
  have := rootS_mem_containersS fam hf; rw [mem_containersS] at this; exact this.1.2

lemma rootS_contains {f : ι} (hf : f ∈ Sstrict fam a b) :
    fam.lo (rootS fam a b f) ≤ fam.lo f ∧ fam.hi f ≤ fam.hi (rootS fam a b f) := by
  have := rootS_mem_containersS fam hf; rw [mem_containersS] at this; exact this.2

/-- The root's width is strictly less than the window's width. -/
lemma rootS_width_lt {f : ι} (hf : f ∈ Sstrict fam a b) :
    fam.hi (rootS fam a b f) - fam.lo (rootS fam a b f) < b - a := by
  obtain ⟨hwlo, hwhi⟩ := rootS_window fam hf
  have hlh := fam.lh (rootS fam a b f) (rootS_mem_E fam hf)
  rcases rootS_strict fam hf with h | h <;> omega

/-- The root is maximal among strict edges. -/
lemma rootS_maximal {f : ι} (hf : f ∈ Sstrict fam a b)
    {g : ι} (hg : g ∈ Sstrict fam a b)
    (h1 : fam.lo g ≤ fam.lo (rootS fam a b f)) (h2 : fam.hi (rootS fam a b f) ≤ fam.hi g) :
    fam.lo g = fam.lo (rootS fam a b f) ∧ fam.hi g = fam.hi (rootS fam a b f) := by
  obtain ⟨hrlo, hrhi⟩ := rootS_contains fam hf
  have hgf : g ∈ containersS fam a b f := by
    rw [mem_containersS]
    rw [mem_Sstrict] at hg
    exact ⟨hg, le_trans h1 hrlo, le_trans hrhi h2⟩
  have hmax := rootS_max fam hf g hgf
  have hlhr := fam.lh (rootS fam a b f) (rootS_mem_E fam hf)
  omega

/-- Root is idempotent. -/
lemma rootS_idem {f : ι} (hf : f ∈ Sstrict fam a b) :
    rootS fam a b (rootS fam a b f) = rootS fam a b f := by
  set r := rootS fam a b f with hr
  have hrS : r ∈ Sstrict fam a b := rootS_mem_Sstrict fam hf
  obtain ⟨hc1, hc2⟩ := rootS_contains fam hrS
  have hmax := rootS_maximal fam hf (rootS_mem_Sstrict fam hrS) hc1 hc2
  exact (fam.inj _ (rootS_mem_E fam hrS) _ (rootS_mem_E fam hf) hmax.1 hmax.2)

/-- The roots in window `(a,b]`: maximal strict edges. -/
noncomputable def Roots (a b : ℕ) : Finset ι :=
  (Sstrict fam a b).filter (fun r => rootS fam a b r = r)

lemma mem_Roots {r : ι} : r ∈ Roots fam a b ↔ r ∈ Sstrict fam a b ∧ rootS fam a b r = r := by
  unfold Roots; rw [mem_filter]

lemma rootS_mem_Roots {f : ι} (hf : f ∈ Sstrict fam a b) : rootS fam a b f ∈ Roots fam a b := by
  rw [mem_Roots]
  exact ⟨rootS_mem_Sstrict fam hf, rootS_idem fam hf⟩

lemma root_self_props {r : ι} (hr : r ∈ Roots fam a b) :
    r ∈ fam.E ∧ a ≤ fam.lo r ∧ fam.hi r ≤ b ∧ (fam.lo r ≠ a ∨ fam.hi r ≠ b) := by
  rw [mem_Roots] at hr
  have := hr.1; rw [mem_Sstrict] at this
  exact ⟨this.1.1, this.1.2.1, this.1.2.2, this.2⟩

/-- Uniqueness: two roots that both contain `g`'s interval coincide. -/
lemma root_unique {r r' : ι} (hr : r ∈ Roots fam a b) (hr' : r' ∈ Roots fam a b)
    {g : ι} (hg : g ∈ fam.E)
    (h1 : fam.lo r ≤ fam.lo g) (h2 : fam.hi g ≤ fam.hi r)
    (h1' : fam.lo r' ≤ fam.lo g) (h2' : fam.hi g ≤ fam.hi r') :
    r = r' := by
  obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
  obtain ⟨hr'E, hr'a, hr'b, hr's⟩ := root_self_props fam hr'
  have hlg := fam.lh g hg
  have hov := overlap_imp_nested fam hrE hr'E (by omega) (by omega)
  rw [mem_Roots] at hr hr'
  have hrS : r ∈ Sstrict fam a b := hr.1
  have hr'S : r' ∈ Sstrict fam a b := hr'.1
  rcases hov with ⟨hle1, hle2⟩ | ⟨hle1, hle2⟩
  · have hmax := rootS_maximal fam hrS hr'S (g := r')
        (by rw [hr.2]; exact hle1) (by rw [hr.2]; exact hle2)
    rw [hr.2] at hmax
    exact fam.inj r hrE r' hr'E (by omega) (by omega)
  · have hmax := rootS_maximal fam hr'S hrS (g := r)
        (by rw [hr'.2]; exact hle1) (by rw [hr'.2]; exact hle2)
    rw [hr'.2] at hmax
    exact fam.inj r hrE r' hr'E (by omega) (by omega)

/-- The fiber of a root `r` equals the subtree `contained (lo r) (hi r)`. -/
lemma fiber_eq_contained {r : ι} (hr : r ∈ Roots fam a b) :
    (Sstrict fam a b).filter (fun g => rootS fam a b g = r) =
      contained fam (fam.lo r) (fam.hi r) := by
  obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
  ext g
  rw [mem_filter, mem_Sstrict, mem_contained]
  constructor
  · rintro ⟨hgS, hgr⟩
    have hgSmem : g ∈ Sstrict fam a b := by rw [mem_Sstrict]; exact hgS
    have hcont := rootS_contains fam hgSmem
    rw [hgr] at hcont
    exact ⟨hgS.1.1, hcont.1, hcont.2⟩
  · rintro ⟨hgE, hglo, hghi⟩
    have hgwin : a ≤ fam.lo g ∧ fam.hi g ≤ b := ⟨le_trans hra hglo, le_trans hghi hrb⟩
    have hglh := fam.lh g hgE
    have hgstrict : fam.lo g ≠ a ∨ fam.hi g ≠ b := by
      rcases hrs with h | h
      · left; omega
      · right; omega
    have hgS : g ∈ Sstrict fam a b := by
      rw [mem_Sstrict]; exact ⟨⟨hgE, hgwin.1, hgwin.2⟩, hgstrict⟩
    refine ⟨⟨⟨hgE, hgwin.1, hgwin.2⟩, hgstrict⟩, ?_⟩
    have hrootg := rootS_mem_Roots fam hgS
    have hcontg := rootS_contains fam hgS
    exact root_unique fam hrootg hr hgE hcontg.1 hcontg.2 hglo hghi

/-- Strict edges decompose as the sum of root subtrees. -/
lemma Sstrict_card_eq_sum :
    (Sstrict fam a b).card = ∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r) := by
  have hmaps : ∀ g ∈ Sstrict fam a b, rootS fam a b g ∈ Roots fam a b :=
    fun g hg => rootS_mem_Roots fam hg
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro r hr
  rw [fiber_eq_contained fam hr]
  rfl

/-- Edges with interval exactly the window. -/
def topEdges (a b : ℕ) : Finset ι :=
  (contained fam a b).filter (fun e => fam.lo e = a ∧ fam.hi e = b)

/-- At most one top edge (intervals identify edges). -/
lemma topEdges_card_le : (topEdges fam a b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  unfold topEdges at hx hy
  rw [mem_filter, mem_contained] at hx hy
  exact fam.inj x hx.1.1 y hy.1.1 (by rw [hx.2.1, hy.2.1]) (by rw [hx.2.2, hy.2.2])

/-- `Sstrict` is the complementary filter to `topEdges`. -/
lemma Sstrict_eq_filter_not :
    Sstrict fam a b = (contained fam a b).filter (fun e => ¬ (fam.lo e = a ∧ fam.hi e = b)) := by
  unfold Sstrict
  apply Finset.filter_congr
  intro e _
  unfold IsStrict
  constructor
  · rintro (h | h) ⟨h1, h2⟩ <;> [exact h h1; exact h h2]
  · intro h
    rw [not_and_or] at h
    exact h

/-- `N = #topEdges + #Sstrict`. -/
lemma N_split : N fam a b = (topEdges fam a b).card + (Sstrict fam a b).card := by
  rw [Sstrict_eq_filter_not]
  unfold N topEdges
  exact (Finset.card_filter_add_card_filter_not (s := contained fam a b)
    (fun e => fam.lo e = a ∧ fam.hi e = b)).symm

/-- Distinct roots have disjoint half-open level-intervals. -/
lemma roots_interval_disjoint {r r' : ι} (hr : r ∈ Roots fam a b) (hr' : r' ∈ Roots fam a b)
    (hne : r ≠ r') : fam.hi r ≤ fam.lo r' ∨ fam.hi r' ≤ fam.lo r := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  rw [not_le] at h1 h2
  obtain ⟨hrE, _, _, _⟩ := root_self_props fam hr
  obtain ⟨hr'E, _, _, _⟩ := root_self_props fam hr'
  have hov := overlap_imp_nested fam hrE hr'E (by omega) (by omega)
  rcases hov with ⟨hle1, hle2⟩ | ⟨hle1, hle2⟩
  · exact hne (root_unique fam hr hr' hrE (le_refl _) (le_refl _) hle1 hle2)
  · exact hne (root_unique fam hr hr' hr'E hle1 hle2 (le_refl _) (le_refl _))

/-- The `Finset.Ioc` intervals of distinct roots are disjoint. -/
lemma roots_Ioc_disjoint :
    (Roots fam a b : Set ι).PairwiseDisjoint (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) := by
  intro r hr r' hr' hne
  simp only [Finset.disjoint_left, Finset.mem_Ioc]
  rintro t ⟨ht1, ht2⟩ ⟨ht3, ht4⟩
  rcases roots_interval_disjoint fam hr hr' hne with h | h <;> omega

/-- Sum of root widths is at most the window width. -/
lemma roots_width_sum_le :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) ≤ b - a := by
  have hcard : ∀ r ∈ Roots fam a b,
      fam.hi r - fam.lo r = (Finset.Ioc (fam.lo r) (fam.hi r)).card := by
    intro r _; rw [Nat.card_Ioc]
  rw [Finset.sum_congr rfl hcard]
  rw [← Finset.card_biUnion (roots_Ioc_disjoint fam)]
  rw [← Nat.card_Ioc a b]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_biUnion] at ht
  obtain ⟨r, hr, htr⟩ := ht
  rw [Finset.mem_Ioc] at htr ⊢
  obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
  omega

/-- THE CRUX: if the window has a top edge, the root subtree widths do not cover it. -/
lemma crux (hab : a < b) (htop : (topEdges fam a b).Nonempty) :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) ≤ b - a - 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hle := roots_width_sum_le fam (a := a) (b := b)
  have hsum : ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) = b - a := by omega
  have hbu : (Roots fam a b).biUnion (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) =
      Finset.Ioc a b := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rw [Finset.mem_biUnion] at ht
      obtain ⟨r, hr, htr⟩ := ht
      rw [Finset.mem_Ioc] at htr ⊢
      obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
      omega
    · rw [Finset.card_biUnion (roots_Ioc_disjoint fam)]
      have : ∑ r ∈ Roots fam a b, (Finset.Ioc (fam.lo r) (fam.hi r)).card
          = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := by
        apply Finset.sum_congr rfl; intro r _; rw [Nat.card_Ioc]
      rw [this, hsum, Nat.card_Ioc]
  obtain ⟨e0, he0⟩ := htop
  unfold topEdges at he0
  rw [mem_filter, mem_contained] at he0
  obtain ⟨⟨he0E, _, _⟩, he0lo, he0hi⟩ := he0
  have hcover : ∀ t, a < t → t ≤ b → ∃ r ∈ Roots fam a b, fam.lo r < t ∧ t ≤ fam.hi r := by
    intro t ht1 ht2
    have htmem : t ∈ Finset.Ioc a b := by rw [Finset.mem_Ioc]; exact ⟨ht1, ht2⟩
    rw [← hbu, Finset.mem_biUnion] at htmem
    obtain ⟨r, hr, htr⟩ := htmem
    rw [Finset.mem_Ioc] at htr
    exact ⟨r, hr, htr.1, htr.2⟩
  have scan : ∀ t, a < t → t ≤ b → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col e0 < fam.col r := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      rcases Nat.lt_or_ge a (t - 1) with hprev | hprev
      · have hprev2 : t - 1 ≤ b := by omega
        obtain ⟨r'', hr'', hr''lo, hr''hi⟩ := hcover (t - 1) hprev hprev2
        have hihr'' := ih (t - 1) (by omega) hprev hprev2 r'' hr'' hr''lo hr''hi
        by_cases hrr : r = r''
        · rw [hrr]; exact hihr''
        · obtain ⟨hr''E, hr''a, hr''b, _⟩ := root_self_props fam hr''
          have hdisj := roots_interval_disjoint fam hr'' hr (fun h => hrr h.symm)
          have hseam1 : fam.hi r'' = t - 1 := by omega
          have hseam2 : fam.lo r = t - 1 := by omega
          have hseam : fam.hi r'' = fam.lo r := by omega
          have hbseam := fam.bSeam r'' hr''E r hrE hseam
          omega
      · have htea : t = a + 1 := by omega
        have hrloa : fam.lo r = a := by omega
        have hrhib : fam.hi r < b := by
          rcases hrs with h | h
          · exact absurd hrloa h
          · omega
        have hbl := fam.bLeft e0 he0E r hrE (by rw [he0lo, hrloa]) (by rw [he0hi]; exact hrhib)
        exact hbl
  obtain ⟨rb, hrb, hrblo, hrbhi⟩ := hcover b (by omega) (le_refl b)
  obtain ⟨hrbE, hrba, hrbb, hrbs⟩ := root_self_props fam hrb
  have hrbhib : fam.hi rb = b := by omega
  have hrbloa : a < fam.lo rb := by
    rcases hrbs with h | h
    · omega
    · exact absurd hrbhib h
  have hscan := scan b (by omega) (le_refl b) rb hrb hrblo hrbhi
  have hbr := fam.bRight e0 he0E rb hrbE (by rw [he0hi, hrbhib]) (by rw [he0lo]; exact hrbloa)
  omega

/-- The master counting bound `N(a,b) ≤ b - a`. -/
theorem master (a b : ℕ) : N fam a b ≤ b - a := by
  induction hw : b - a using Nat.strongRecOn generalizing a b with
  | ind w ih =>
    rcases Nat.lt_or_ge a b with hab | hba
    · rw [N_split fam]
      rw [Sstrict_card_eq_sum fam]
      have hsub : ∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r)
          ≤ ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hwlt : fam.hi r - fam.lo r < w := by
          rw [mem_Roots] at hr
          have := rootS_width_lt fam hr.1
          rw [hr.2] at this
          omega
        exact ih (fam.hi r - fam.lo r) hwlt (fam.lo r) (fam.hi r) rfl
      rcases Finset.eq_empty_or_nonempty (topEdges fam a b) with htop | htop
      · rw [htop, Finset.card_empty]
        have := roots_width_sum_le fam (a := a) (b := b)
        omega
      · have hc := crux fam hab htop
        have htle := topEdges_card_le fam (a := a) (b := b)
        omega
    · rw [N_eq_zero_of_le fam hba]; omega

end AbstractLaminar

/-! # PART II — The geometric edge model (edges = survivors) and the forward bound. -/

namespace CriticalPortraits

open Finset
open scoped BigOperators

/-! ## Phase -1: arithmetic engine reused everywhere. -/

/-- `i.val = (i.val % m) + (i.val / m) * m`. -/
lemma val_decomp {N m : ℕ} (i : ZMod N) : i.val = (i.val % m) + (i.val / m) * m := by
  have := Nat.div_add_mod' i.val m; omega

/-- ENGINE: a single level of separation beats any column offset, ANY fibers. -/
lemma sameblock_lt {N m : ℕ} (hm : 0 < m) {x y : ZMod N}
    (ha : x.val / m < y.val / m) : x.val < y.val := by
  have hp : x.val % m < m := Nat.mod_lt _ hm
  have hq : y.val % m < m := Nat.mod_lt _ hm
  have hx := val_decomp (m := m) x; have hy := val_decomp (m := m) y
  have := sep_master (m := m) (p := x.val % m) (q := y.val % m)
      (a := x.val / m) (c := y.val / m) hp hq ha
  omega

/-- Members of a critical set share a fiber (column). -/
lemma critical_sameFiber {d m : ℕ} {S : Finset (ZMod (d * m))} (hS : IsCriticalSet d m S)
    {x y : ZMod (d * m)} (hx : x ∈ S) (hy : y ∈ S) : x.val % m = y.val % m := by
  obtain ⟨⟨r, hr, hfib⟩, _⟩ := hS; rw [hfib _ hx, hfib _ hy]

/-! ## Phase 0a: host-set recovery (the edge's home critical set). -/

variable {d m : ℕ}

/-- The host critical set of an edge `x` in `T P`. -/
noncomputable def hostSet (P : Finset (Finset (ZMod (d * m)))) (x : ZMod (d * m))
    (hx : x ∈ T P) : Finset (ZMod (d*m)) := (mem_T.mp hx).choose

lemma hostSet_mem {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)} (hx : x ∈ T P) :
    hostSet P x hx ∈ P := (mem_T.mp hx).choose_spec.1

lemma mem_eraseMin_hostSet {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)} (hx : x ∈ T P) :
    x ∈ eraseMin (hostSet P x hx) := (mem_T.mp hx).choose_spec.2

lemma mem_hostSet {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)} (hx : x ∈ T P) :
    x ∈ hostSet P x hx := eraseMin_subset _ (mem_eraseMin_hostSet hx)

/-! ## Phase 0b: predecessor = the other endpoint (immediate predecessor in the host). -/

/-- The elements of `S` strictly below `x` in value. -/
def belowIn (S : Finset (ZMod (d * m))) (x : ZMod (d * m)) : Finset (ZMod (d * m)) :=
  S.filter (fun y => y.val < x.val)

lemma belowIn_nonempty [NeZero (d * m)] {S : Finset (ZMod (d * m))} (h : S.Nonempty)
    {x : ZMod (d * m)} (hx : x ∈ eraseMin S) : (belowIn S x).Nonempty := by
  refine ⟨minVal S h, ?_⟩
  rw [belowIn, mem_filter]
  refine ⟨minVal_mem S h, ?_⟩
  have hxS := eraseMin_subset S hx
  have hxne := ((mem_eraseMin S h x).mp hx).2
  rcases lt_or_eq_of_le (minVal_le S h x hxS) with hlt | heq
  · exact hlt
  · exact absurd (ZMod.val_injective _ heq).symm hxne

/-- The immediate predecessor of survivor `x` inside its host set: the `.val`-greatest
    element of the host strictly below `x`. -/
noncomputable def predIn [NeZero (d * m)] (P : Finset (Finset (ZMod (d * m)))) (x : ZMod (d * m))
    (hx : x ∈ T P) : ZMod (d*m) := by
  classical
  exact (Finset.exists_max_image (belowIn (hostSet P x hx) x) (fun y => y.val)
    (belowIn_nonempty ⟨x, mem_hostSet hx⟩ (mem_eraseMin_hostSet hx))).choose

lemma predIn_mem_belowIn [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : predIn P x hx ∈ belowIn (hostSet P x hx) x :=
  (Finset.exists_max_image (belowIn (hostSet P x hx) x) (fun y => y.val)
    (belowIn_nonempty ⟨x, mem_hostSet hx⟩ (mem_eraseMin_hostSet hx))).choose_spec.1

lemma predIn_max [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : ∀ y ∈ belowIn (hostSet P x hx) x, y.val ≤ (predIn P x hx).val :=
  (Finset.exists_max_image (belowIn (hostSet P x hx) x) (fun y => y.val)
    (belowIn_nonempty ⟨x, mem_hostSet hx⟩ (mem_eraseMin_hostSet hx))).choose_spec.2

lemma predIn_mem_host [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : predIn P x hx ∈ hostSet P x hx :=
  (mem_filter.mp (predIn_mem_belowIn hx)).1

lemma predIn_val_lt [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : (predIn P x hx).val < x.val :=
  (mem_filter.mp (predIn_mem_belowIn hx)).2

/-- The host set of a survivor is critical. -/
lemma hostSet_critical {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) {x : ZMod (d * m)}
    (hx : x ∈ T P) : IsCriticalSet d m (hostSet P x hx) := hP.1 _ (hostSet_mem hx)

/-- Predecessor shares the survivor's fiber. -/
lemma predIn_sameFiber [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x : ZMod (d * m)} (hx : x ∈ T P) : (predIn P x hx).val % m = x.val % m :=
  critical_sameFiber (hostSet_critical hP hx) (predIn_mem_host hx) (mem_hostSet hx)

/-- The edge is nonempty: `lo < hi` in level. -/
lemma predIn_level_lt (hd : 0 < d) (hm : 0 < m) {P : Finset (Finset (ZMod (d * m)))}
    (hP : Portrait d m P) {x : ZMod (d * m)} (hx : x ∈ T P) :
    haveI : NeZero (d*m) := ⟨by positivity⟩
    (predIn P x hx).val / m < x.val / m := by
  haveI : NeZero (d*m) := ⟨by positivity⟩
  have hsame := predIn_sameFiber hP hx
  have hvlt := predIn_val_lt hx
  rcases lt_or_eq_of_le ((val_le_iff_level_le_of_sameFiber hsame).mp hvlt.le) with hlt | heq
  · exact hlt
  · exact absurd (congrArg ZMod.val (level_injOn_fiber hsame heq)) (Nat.ne_of_lt hvlt)

/-- `predIn x` is the immediate predecessor: no host element strictly between it and `x`. -/
lemma predIn_immediate [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) {z : ZMod (d * m)} (hz : z ∈ hostSet P x hx)
    (h1 : (predIn P x hx).val < z.val) (h2 : z.val < x.val) : False := by
  have hzb : z ∈ belowIn (hostSet P x hx) x := by
    rw [belowIn, mem_filter]; exact ⟨hz, h2⟩
  have := predIn_max hx z hzb
  omega

/-! ## Phase 1: the crossing engine. -/

/-- Cross-host crossing: an alternating val-quadruple `px < py < x < y` with `px,x` in host `x`
    and `py,y` in host `y` (distinct hosts) contradicts the portrait's Unlinked clause. -/
lemma cross_false [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P)
    (hhost : hostSet P x hx ≠ hostSet P y hy)
    (o1 : (predIn P x hx).val < (predIn P y hy).val)
    (o2 : (predIn P y hy).val < x.val)
    (o3 : x.val < y.val) : False := by
  have hL : Linked (hostSet P x hx) (hostSet P y hy) :=
    linked_of_lt (predIn_mem_host hx) (mem_hostSet hx) (predIn_mem_host hy) (mem_hostSet hy)
      o1 o2 o3
  exact (hP.2.2.1 _ (hostSet_mem hx) _ (hostSet_mem hy) hhost) hL

/-! ## Phase 2: total edge data `(loV, hiV, colV)`. -/

/-- The level index `x.val / m` of a position `x`. -/
def hiV (x : ZMod (d * m)) : ℕ := x.val / m
/-- The fiber index `x.val % m` of a position `x`. -/
def colV (x : ZMod (d * m)) : ℕ := x.val % m
/-- The low interval-endpoint value of `x` within its host critical set. -/
noncomputable def loV [NeZero (d * m)] (P : Finset (Finset (ZMod (d * m))))
    (x : ZMod (d * m)) : ℕ :=
  if hx : x ∈ T P then (predIn P x hx).val / m else 0

lemma loV_eq [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) :
    loV P x = (predIn P x hx).val / m := by
  unfold loV; rw [dif_pos hx]

/-- The survivor's value decomposes as `colV + hiV*m`. -/
lemma top_val_eq {x : ZMod (d * m)} : x.val = colV x + hiV x * m := by
  unfold colV hiV; have := Nat.div_add_mod' x.val m; omega

/-- The predecessor's value decomposes as `colV + loV*m` (same column as the survivor). -/
lemma pred_val_eq [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x : ZMod (d * m)} (hx : x ∈ T P) : (predIn P x hx).val = colV x + loV P x * m := by
  have hsame := predIn_sameFiber hP hx
  rw [loV_eq hx]
  unfold colV
  rw [← hsame]
  have := Nat.div_add_mod' (predIn P x hx).val m; omega

/-! ## Phase 3: the master non-alternation + same-host glue. -/

/-- THE MASTER NON-ALTERNATION LEMMA. No two survivors' endpoints alternate as
    `px < py < x < y` (covers cross-host via Unlinked and same-host via immediacy). -/
lemma no_alt [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P)
    (o1 : (predIn P x hx).val < (predIn P y hy).val)
    (o2 : (predIn P y hy).val < x.val)
    (o3 : x.val < y.val) : False := by
  by_cases hhost : hostSet P x hx = hostSet P y hy
  · -- same host: predIn y lies strictly between predIn x and x, in host x
    apply predIn_immediate hx (z := predIn P y hy) ?_ o1 o2
    rw [hhost]; exact predIn_mem_host hy
  · exact cross_false hP hx hy hhost o1 o2 o3

/-- If two survivors coincide as points they share a host (Portrait disjointness). -/
lemma eq_imp_sameHost {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P) (hxy : x = y) :
    hostSet P x hx = hostSet P y hy := by
  by_contra hne
  have hdisj := hP.2.1 _ (hostSet_mem hx) _ (hostSet_mem hy) hne
  have hmemx : x ∈ hostSet P x hx := mem_hostSet hx
  have hmemy : x ∈ hostSet P y hy := hxy ▸ mem_hostSet hy
  exact (Finset.disjoint_left.mp hdisj hmemx) hmemy

/-- If predecessors coincide as points the survivors share a host. -/
lemma predEq_imp_sameHost {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P)
    [NeZero (d * m)] (hpe : predIn P x hx = predIn P y hy) :
    hostSet P x hx = hostSet P y hy := by
  by_contra hne
  have hdisj := hP.2.1 _ (hostSet_mem hx) _ (hostSet_mem hy) hne
  have hmemx : predIn P x hx ∈ hostSet P x hx := predIn_mem_host hx
  have hmemy : predIn P x hx ∈ hostSet P y hy := hpe ▸ predIn_mem_host hy
  exact (Finset.disjoint_left.mp hdisj hmemx) hmemy

/-! ## Phase 4: the LEMMA A / LEMMA B / inj axioms (in `loV/hiV/colV`). -/

lemma colV_lt_m (hm : 0 < m) (x : ZMod (d * m)) : colV x < m := Nat.mod_lt _ hm

/-- LEMMA A: laminar (no proper overlap of level-intervals). -/
lemma lemmaA [NeZero (d * m)] (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (h1 : loV P e < loV P f) (h2 : loV P f < hiV e) (h3 : hiV e < hiV f) : False := by
  -- build the alternation px < py < e.val < f.val
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  -- o1: predIn e .val < predIn f .val   (loV e < loV f)
  have o1 : (predIn P e he).val < (predIn P f hf).val := by
    rw [hpe, hpf]; have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf h1; omega
  -- o2: predIn f .val < e.val   (loV f < hiV e)
  have o2 : (predIn P f hf).val < e.val := by
    rw [hpf, hte]; have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce h2; omega
  -- o3: e.val < f.val   (hiV e < hiV f)
  have o3 : e.val < f.val := by
    rw [hte, htf]; have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf h3; omega
  exact no_alt hP he hf o1 o2 o3

/-- LEMMA B (seam): `e` tops where `f` bottoms ⇒ `col e ≤ col f`. -/
lemma lemmaB_seam [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P) (hseam : hiV e = loV P f) :
    colV e ≤ colV f := by
  by_contra hc
  rw [not_le] at hc  -- colV f < colV e
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hlhe : loV P e < hiV e := by rw [loV_eq he]; exact predIn_level_lt hd hm hP he
  have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
  -- o1: predIn e .val < predIn f .val
  have o1 : (predIn P e he).val < (predIn P f hf).val := by
    rw [hpe, hpf, ← hseam]
    have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlhe
    omega
  -- o2: predIn f .val < e.val
  have o2 : (predIn P f hf).val < e.val := by
    rw [hpf, hte, ← hseam]; omega
  -- o3: e.val < f.val
  have o3 : e.val < f.val := by
    rw [hte, htf]
    have hef : hiV e < hiV f := by rw [hseam]; exact hlhf
    have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hef
    omega
  exact no_alt hP he hf o1 o2 o3

/-- LEMMA B (right-aligned): share top, nested right ⇒ inner col smaller. -/
lemma lemmaB_right [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (htop : hiV e = hiV f) (hlo : loV P e < loV P f) : colV f < colV e := by
  by_contra hc
  rw [not_lt] at hc  -- colV e ≤ colV f
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
  rcases lt_or_eq_of_le hc with hclt | hceq
  · -- colV e < colV f: alternation e,f
    have o1 : (predIn P e he).val < (predIn P f hf).val := by
      rw [hpe, hpf]
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlo
      omega
    have o2 : (predIn P f hf).val < e.val := by
      rw [hpf, hte]
      have hlt : loV P f < hiV e := by rw [htop]; exact hlhf
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hlt
      omega
    have o3 : e.val < f.val := by
      rw [hte, htf, ← htop]; omega
    exact no_alt hP he hf o1 o2 o3
  · -- colV e = colV f ⇒ e = f ⇒ loV e = loV f, contra loV e < loV f
    have hval : e.val = f.val := by rw [hte, htf, htop, hceq]
    have : e = f := ZMod.val_injective _ hval
    rw [this] at hlo; omega

/-- LEMMA B (left-aligned): share bottom, nested left ⇒ inner col larger. -/
lemma lemmaB_left [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (hbot : loV P e = loV P f) (hhi : hiV f < hiV e) : colV e < colV f := by
  by_contra hc
  rw [not_lt] at hc  -- colV f ≤ colV e
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
  rcases lt_or_eq_of_le hc with hclt | hceq
  · -- colV f < colV e: alternation f,e
    have o1 : (predIn P f hf).val < (predIn P e he).val := by
      rw [hpf, hpe, ← hbot]; omega
    have o2 : (predIn P e he).val < f.val := by
      rw [hpe, htf, hbot]
      have hlt : loV P f < hiV f := hlhf
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlt
      omega
    have o3 : f.val < e.val := by
      rw [htf, hte]
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hhi
      omega
    exact no_alt hP hf he o1 o2 o3
  · -- colV f = colV e ⇒ predIn e = predIn f ⇒ same host ⇒ f between p and e ⇒ immediacy
    have hpv : (predIn P e he).val = (predIn P f hf).val := by rw [hpe, hpf, hbot, hceq]
    have hpeq : predIn P e he = predIn P f hf := ZMod.val_injective _ hpv
    have hhost := predEq_imp_sameHost hP he hf hpeq
    -- f ∈ hostSet e
    have hfmem : f ∈ hostSet P e he := by rw [hhost]; exact mem_hostSet hf
    -- p.val < f.val < e.val
    have hlt1 : (predIn P e he).val < f.val := by
      rw [hpe, htf, hbot]
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlhf
      omega
    have hlt2 : f.val < e.val := by
      rw [htf, hte]
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hhi
      omega
    exact predIn_immediate he hfmem hlt1 hlt2

/-- INJECTIVITY: distinct survivors have distinct level-intervals. -/
lemma edge_inj [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (hlo : loV P e = loV P f) (hhi : hiV e = hiV f) : e = f := by
  by_contra hne
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hlhe : loV P e < hiV e := by rw [loV_eq he]; exact predIn_level_lt hd hm hP he
  -- colV e ≠ colV f (else same val ⇒ equal)
  have hcne : colV e ≠ colV f := by
    intro h
    exact hne (ZMod.val_injective _ (by rw [hte, htf, hhi, h]))
  rcases Nat.lt_or_ge (colV e) (colV f) with hclt | hcge
  · -- alternation e,f
    have o1 : (predIn P e he).val < (predIn P f hf).val := by rw [hpe, hpf, hlo]; omega
    have o2 : (predIn P f hf).val < e.val := by
      rw [hpf, hte, ← hlo]
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hlhe
      omega
    have o3 : e.val < f.val := by rw [hte, htf, ← hhi]; omega
    exact no_alt hP he hf o1 o2 o3
  · -- colV f < colV e (since ≠): alternation f,e
    have hclt : colV f < colV e := lt_of_le_of_ne hcge (fun h => hcne h.symm)
    have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
    have o1 : (predIn P f hf).val < (predIn P e he).val := by rw [hpf, hpe, ← hlo]; omega
    have o2 : (predIn P e he).val < f.val := by
      rw [hpe, htf, hlo]
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlhf
      omega
    have o3 : f.val < e.val := by rw [htf, hte, hhi]; omega
    exact no_alt hP hf he o1 o2 o3

/-! ## Phase 5: the `Family` instance and the forward bound. -/

/-- The laminar interval family of a portrait's survivors (edges = survivors). -/
noncomputable def survivorFamily [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    AbstractLaminar.Family (ZMod (d*m)) where
  E := T P
  lo := loV P
  hi := hiV
  col := colV
  lh := fun e he => by rw [loV_eq he]; exact predIn_level_lt hd hm hP he
  inj := fun e he f hf hlo hhi => edge_inj hd hm hP he hf hlo hhi
  laminar := fun e he f hf => fun ⟨h1, h2, h3⟩ => lemmaA hm hP he hf h1 h2 h3
  bRight := fun e he f hf htop hlo => lemmaB_right hd hm hP he hf htop hlo
  bLeft := fun e he f hf hbot hhi => lemmaB_left hd hm hP he hf hbot hhi
  bSeam := fun e he f hf hseam => lemmaB_seam hd hm hP he hf hseam

/-- **FORWARD BOUND.** `T P` is level-canonical, for every degree `d`. -/
theorem T_levelCanonical {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    LevelCanonical d m (T P) := by
  haveI : NeZero (d*m) := ⟨by positivity⟩
  intro j hj
  -- The LevelCanonical filter equals `contained (survivorFamily) 0 j`.
  have hfilter : (T P).filter (fun i => i.val / m ≤ j)
      = AbstractLaminar.contained (survivorFamily hd hm hP) 0 j := by
    unfold AbstractLaminar.contained
    apply Finset.filter_congr
    intro e he
    constructor
    · intro h; exact ⟨Nat.zero_le _, h⟩
    · intro h; exact h.2
  rw [hfilter]
  have hm0 := AbstractLaminar.master (survivorFamily hd hm hP) 0 j
  unfold AbstractLaminar.N at hm0
  simpa using hm0

end CriticalPortraits
