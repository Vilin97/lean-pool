/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/

import LeanPool.CriticalPortraits.Forward

/-!
# INJECTIVITY of `T` (Brick 4).

`T` is injective on critical portraits, for every degree `d`:

  `T_injOn : Set.InjOn (T (N := d*m)) {P | Portrait d m P}`

uses the REAL `Portraits.T` (`= P.sup eraseMin`) and `Portraits.Portrait`.

Bottom-up build (paper Part I — Uniqueness):
  PART A  (`AbstractLaminar`)  — the TIGHTNESS / equality layer on top of `master`
                                (`root_saturated`, `edge_tight_of_saturated`) and
                                COLUMN-SEPARATION (`column_sep`).
  PART B  (`CriticalPortraits`)           — geometric TIGHTNESS / column-sep at the survivor family,
                                Lemma 2 (block-span laminarity), the BRIDGE edge core, the
                                blocks-as-host-sets recovery, and the injectivity assembly.

STATUS: FULLY SORRY-FREE.  The keystone `predIn_forced` (paper Part I, stage 1: the inductive
forced-predecessor / Structural-Lemma dispatch — the documented all-`d` kernel) is now CLOSED for
all `d` via the spanning-edge kernel (`spanning_edge`), built from the directional column
separation (`column_sep_with_gap` / `column_sep_geom_dir`).  Everything is axiom-clean
(`{propext, Classical.choice, Quot.sound}`, NO `sorryAx`, NO `native_decide`), including:
  • PART A TIGHTNESS  (`root_saturated`, `edge_tight_of_saturated`) and COLUMN-SEPARATION
    (`column_sep`, `column_sep_with_gap`) — degree-free, axiom-clean.
  • PART B geometric TIGHTNESS / column-sep (`edge_tight_geom`, `column_sep_geom`,
    `column_sep_geom_dir`), Lemma 2 (`span_laminar`), the BRIDGE edge core (`bridge_edge`).
  • Stage 1 keystone: `predIn_forced` — PROVED (strong induction on `.val` + WLOG + the
    spanning-edge crossing into `no_alt`).
  • Stage 2 (component recovery): `hostSet_forced` from `predIn_forced`.
  • The assembly `T_inj` / `T_injOn`.
-/

open Finset
open scoped BigOperators

/-! ## PART A — TIGHTNESS in `AbstractLaminar`. -/

namespace AbstractLaminar

variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)

/-- **Saturation propagates to roots.** If the window `(a,b]` is saturated
    (`N = b-a`), then every root's subtree is itself saturated. -/
lemma root_saturated {a b : ℕ} (hsat : N fam a b = b - a) :
    ∀ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r) = fam.hi r - fam.lo r := by
  -- The master chain, but tracking equality.
  rcases Nat.lt_or_ge a b with hab | hba
  · -- termwise bound N(lo r, hi r) ≤ hi r - lo r
    have hterm : ∀ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r) ≤ fam.hi r - fam.lo r := by
      intro r _; exact master fam _ _
    -- ∑ N(lo r, hi r) = #Sstrict (forest decomposition)
    have hSstrict := Sstrict_card_eq_sum fam (a := a) (b := b)
    -- N = #top + #Sstrict
    have hNsplit := N_split fam (a := a) (b := b)
    have htle := topEdges_card_le fam (a := a) (b := b)
    have hwidth := roots_width_sum_le fam (a := a) (b := b)
    -- Show ∑ N(lo r, hi r) = ∑ (hi r - lo r), then conclude pointwise.
    have hsumeq : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r))
        = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := by
      -- ≤ direction is termwise.
      have hle : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r))
          ≤ ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := Finset.sum_le_sum hterm
      -- Now lower bound ∑ N(lo r,hi r) using the saturation.
      rcases Finset.eq_empty_or_nonempty (topEdges fam a b) with htop | htop
      · -- no top edge: #Sstrict = N = b - a, and ∑(hi-lo) ≤ b-a.
        rw [htop, Finset.card_empty] at hNsplit
        -- hNsplit : N = 0 + #Sstrict
        have : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r)) = b - a := by
          rw [← hSstrict]; omega
        omega
      · -- top edge present: crux gives ∑(hi-lo) ≤ b-a-1, #top = 1, #Sstrict = N - 1.
        have hcrux := crux fam hab htop
        have htpos : 1 ≤ (topEdges fam a b).card := Finset.card_pos.mpr htop
        have htone : (topEdges fam a b).card = 1 := le_antisymm htle htpos
        have : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r)) = b - a - 1 := by
          rw [← hSstrict]; omega
        omega
    -- pointwise equality.
    exact (Finset.sum_eq_sum_iff_of_le hterm).mp hsumeq
  · -- empty window
    intro r hr
    obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
    -- if b ≤ a then there are no roots (window empty) — contradiction or vacuous.
    have hlh := fam.lh r hrE
    omega

/-- **Every edge is tight.** If the window `(a,b]` is saturated, then every edge contained in
    it has a saturated own-window (`N(lo e, hi e) = hi e - lo e`, i.e. `g(e) = h(e) - 1`). -/
lemma edge_tight_of_saturated :
    ∀ w : ℕ, ∀ a b : ℕ, b - a = w → N fam a b = b - a →
      ∀ e ∈ contained fam a b, N fam (fam.lo e) (fam.hi e) = fam.hi e - fam.lo e := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro a b hw hsat e he
    rw [mem_contained] at he
    obtain ⟨heE, hea, heb⟩ := he
    by_cases htop : fam.lo e = a ∧ fam.hi e = b
    · -- e is the top edge: its window IS the saturated window.
      rw [htop.1, htop.2]; rw [hsat]
    · -- e is strict; its root is saturated, and the root window is smaller.
      have heS : e ∈ Sstrict fam a b := by
        rw [mem_Sstrict]
        refine ⟨⟨heE, hea, heb⟩, ?_⟩
        rw [not_and_or] at htop; exact htop
      have hr := rootS_mem_Roots fam heS
      have hrsat := root_saturated fam hsat _ hr
      have hcont := rootS_contains fam heS
      -- e contained in (lo r, hi r)
      have hewin : e ∈ contained fam (fam.lo (rootS fam a b e)) (fam.hi (rootS fam a b e)) := by
        rw [mem_contained]; exact ⟨heE, hcont.1, hcont.2⟩
      -- root window width < w
      have hrwidth := rootS_width_lt fam heS
      exact ih (fam.hi (rootS fam a b e) - fam.lo (rootS fam a b e)) (by omega)
        (fam.lo (rootS fam a b e)) (fam.hi (rootS fam a b e)) rfl hrsat e hewin

/-! ### A2 — COLUMN-SEPARATION.

For a saturated window `(a,b]` whose top edge `e0` exists (interval exactly `(a,b]`), every root
`r` has `col r ≠ col e0`.  Proof by the seam scan: the gap splits roots into a left run (each
shares the bottom `a` up to the gap; `bLeft`/`bSeam` ⇒ `col e0 < col r`) and a right run (each
shares the top `b` down to the gap; `bRight`/`bSeam` ⇒ `col r < col e0`). -/

/-- Saturated window with a top edge: the root subtree widths sum to exactly `b - a - 1`. -/
lemma roots_width_sum_eq {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    (htop : (topEdges fam a b).Nonempty) :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) = b - a - 1 := by
  -- each root saturated ⇒ ∑ N(lo,hi) = ∑ widths.
  have hrsat := root_saturated fam hsat
  have hcongr : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r))
      = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) :=
    Finset.sum_congr rfl (fun r hr => hrsat r hr)
  have hSstrict := Sstrict_card_eq_sum fam (a := a) (b := b)
  have hNsplit := N_split fam (a := a) (b := b)
  have htone : (topEdges fam a b).card = 1 :=
    le_antisymm (topEdges_card_le fam) (Finset.card_pos.mpr htop)
  -- N = 1 + #Sstrict = 1 + ∑ widths; N = b - a; so ∑ widths = b - a - 1
  rw [htone] at hNsplit
  rw [hSstrict, hcongr] at hNsplit
  omega

/-- The root level-intervals of a saturated top-edged window miss exactly one level `g*`:
    there is a unique `g ∈ (a,b]` covered by no root. -/
lemma exists_gap {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    (htop : (topEdges fam a b).Nonempty) :
    ∃ g, a < g ∧ g ≤ b ∧ (∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r)) := by
  -- biUnion of root Iocs has card = ∑ widths = b-a-1 < b-a = card (Ioc a b), and is a subset.
  set B := (Roots fam a b).biUnion (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) with hB
  have hsub : B ⊆ Finset.Ioc a b := by
    intro t ht
    rw [hB, Finset.mem_biUnion] at ht
    obtain ⟨r, hr, htr⟩ := ht
    rw [Finset.mem_Ioc] at htr ⊢
    obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
    omega
  have hcardB : B.card = b - a - 1 := by
    rw [hB, Finset.card_biUnion (roots_Ioc_disjoint fam)]
    have : ∑ r ∈ Roots fam a b, (Finset.Ioc (fam.lo r) (fam.hi r)).card
        = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) :=
      Finset.sum_congr rfl (fun r _ => Nat.card_Ioc _ _)
    rw [this, roots_width_sum_eq fam hab hsat htop]
  -- so B is a proper subset of Ioc a b, missing exactly one element.
  have hcardIoc : (Finset.Ioc a b).card = b - a := Nat.card_Ioc a b
  have hssub : B ⊂ Finset.Ioc a b := by
    rw [Finset.ssubset_iff_of_subset hsub]
    by_contra hc
    push Not at hc
    have : Finset.Ioc a b ⊆ B := hc
    have := Finset.card_le_card this
    omega
  obtain ⟨g, hgIoc, hgB⟩ := Finset.exists_of_ssubset hssub
  rw [Finset.mem_Ioc] at hgIoc
  refine ⟨g, hgIoc.1, hgIoc.2, ?_⟩
  intro r hr ⟨h1, h2⟩
  apply hgB
  rw [hB, Finset.mem_biUnion]
  exact ⟨r, hr, by rw [Finset.mem_Ioc]; exact ⟨h1, h2⟩⟩

/-- Every level in `(a,b]` except the gap `g` (with `a < g ≤ b`) is covered by some root. -/
lemma covered_of_ne_gap {a b g : ℕ} (htop : (topEdges fam a b).Nonempty)
    (hsat : N fam a b = b - a) (hab : a < b)
    (hg1 : a < g) (hg2 : g ≤ b)
    (hgap : ∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r))
    {t : ℕ} (ht1 : a < t) (ht2 : t ≤ b) (htne : t ≠ g) :
    ∃ r ∈ Roots fam a b, fam.lo r < t ∧ t ≤ fam.hi r := by
  set B := (Roots fam a b).biUnion (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) with hB
  have hsub : B ⊆ Finset.Ioc a b := by
    intro s hs
    rw [hB, Finset.mem_biUnion] at hs
    obtain ⟨r, hr, hsr⟩ := hs
    rw [Finset.mem_Ioc] at hsr ⊢
    obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
    omega
  have hcardB : B.card = b - a - 1 := by
    rw [hB, Finset.card_biUnion (roots_Ioc_disjoint fam)]
    have : ∑ r ∈ Roots fam a b, (Finset.Ioc (fam.lo r) (fam.hi r)).card
        = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) :=
      Finset.sum_congr rfl (fun r _ => Nat.card_Ioc _ _)
    rw [this, roots_width_sum_eq fam hab hsat htop]
  have hgnotB : g ∉ B := by
    rw [hB, Finset.mem_biUnion]; push Not
    intro r hr
    rw [Finset.mem_Ioc]
    intro ⟨h1, h2⟩
    exact hgap r hr ⟨h1, h2⟩
  have hgIoc : g ∈ Finset.Ioc a b := by rw [Finset.mem_Ioc]; exact ⟨hg1, hg2⟩
  -- insert g B ⊆ Ioc a b with card (b-a-1)+1 = b-a = card Ioc ⇒ insert g B = Ioc a b.
  have hins_sub : insert g B ⊆ Finset.Ioc a b := Finset.insert_subset hgIoc hsub
  have hins_card : (insert g B).card = b - a := by
    rw [Finset.card_insert_of_notMem hgnotB, hcardB]
    have hbpos : 1 ≤ b - a := by omega
    omega
  have heq : insert g B = Finset.Ioc a b :=
    Finset.eq_of_subset_of_card_le hins_sub (by rw [hins_card, Nat.card_Ioc])
  -- t ∈ Ioc a b, t ≠ g ⇒ t ∈ B
  have htIoc : t ∈ Finset.Ioc a b := by rw [Finset.mem_Ioc]; exact ⟨ht1, ht2⟩
  rw [← heq, Finset.mem_insert] at htIoc
  rcases htIoc with h | h
  · exact absurd h htne
  · rw [hB, Finset.mem_biUnion] at h
    obtain ⟨r, hr, htr⟩ := h
    rw [Finset.mem_Ioc] at htr
    exact ⟨r, hr, htr.1, htr.2⟩

/-- Distinct roots covering adjacent levels seam: if `r''` covers `s` and `r` covers a level just
    above `s` (with `lo r < s+1`), and `r'' ≠ r`, then `hi r'' = lo r`.  (Used in the seam scan.) -/
lemma seam_of_adjacent {a b : ℕ} {r'' r : ι} (hr'' : r'' ∈ Roots fam a b) (hr : r ∈ Roots fam a b)
    {s : ℕ} (hs1 : fam.lo r'' < s) (hs2 : s ≤ fam.hi r'')
    (hrhi : s + 1 ≤ fam.hi r) (hadj : fam.lo r = s) : fam.hi r'' = s := by
  -- r'' covers s, r covers s+1; if hi r'' ≥ s+1, both Iocs contain s+1 (disjoint) ⇒ contra
  rcases roots_interval_disjoint fam hr'' hr (by
      intro h; rw [h] at hs1 hs2; omega) with hd | hd
  · omega
  · omega

/-- **COLUMN-SEPARATION (abstract).** For a saturated window `(a,b]` with a top edge `e0`, every
    root has column `≠ col e0`. -/
lemma column_sep {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    {e0 : ι} (he0E : e0 ∈ fam.E) (he0lo : fam.lo e0 = a) (he0hi : fam.hi e0 = b) :
    ∀ r ∈ Roots fam a b, fam.col r ≠ fam.col e0 := by
  -- top edge present
  have htop : (topEdges fam a b).Nonempty := by
    refine ⟨e0, ?_⟩
    unfold topEdges; rw [Finset.mem_filter, mem_contained]
    exact ⟨⟨he0E, by omega, by omega⟩, he0lo, he0hi⟩
  obtain ⟨g, hg1, hg2, hgap⟩ := exists_gap fam hab hsat htop
  -- LEFT SCAN: roots covering levels in (a, g) have col e0 < col r.
  have scanLeft : ∀ t, a < t → t < g → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col e0 < fam.col r := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      -- r is a left root: hi r < g.
      have hrhig : fam.hi r < g := by
        by_contra hc
        push Not at hc  -- g ≤ hi r
        exact hgap r hr ⟨by omega, hc⟩
      by_cases hlo : fam.lo r = a
      · -- bottom-most: shares bottom with e0
        have hbl := fam.bLeft e0 he0E r hrE (by rw [he0lo, hlo]) (by rw [he0hi]; omega)
        exact hbl
      · -- lo r > a; find seam predecessor covering lo r
        have hloa : a < fam.lo r := by omega
        have hlog : fam.lo r < g := by omega
        have hlone : fam.lo r ≠ g := by omega
        obtain ⟨r'', hr'', hr''lo, hr''hi⟩ :=
          covered_of_ne_gap fam htop hsat hab hg1 hg2 hgap hloa (by omega) hlone
        have hrr : r'' ≠ r := by
          intro h; rw [h] at hr''hi hr''lo; omega
        have hseam : fam.hi r'' = fam.lo r :=
          seam_of_adjacent fam hr'' hr hr''lo hr''hi (by omega) rfl
        have hih := ih (fam.lo r) (by omega) hloa hlog r'' hr'' hr''lo hr''hi
        have hbseam := fam.bSeam r'' (root_self_props fam hr'').1 r hrE hseam
        omega
  -- RIGHT SCAN: roots covering levels in (g, b] have col r < col e0. Induct on (b - t) so the
  -- inductive step can reach the seam successor (a LARGER level).
  have scanRight : ∀ n t, b - t = n → g < t → t ≤ b → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col r < fam.col e0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t hn ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      by_cases hhi : fam.hi r = b
      · -- top-most: shares top with e0
        have hbr := fam.bRight e0 he0E r hrE (by rw [he0hi, hhi]) (by rw [he0lo]; omega)
        exact hbr
      · -- hi r < b; find seam successor covering hi r + 1
        have hhib : fam.hi r < b := by omega
        have hsucc1 : g < fam.hi r + 1 := by omega
        have hsucc2 : fam.hi r + 1 ≤ b := by omega
        have hsuccne : fam.hi r + 1 ≠ g := by omega
        obtain ⟨r', hr', hr'lo, hr'hi⟩ :=
          covered_of_ne_gap fam htop hsat hab hg1 hg2 hgap (by omega) hsucc2 hsuccne
        have hrr : r' ≠ r := by
          intro h; rw [h] at hr'lo hr'hi; omega
        -- seam: hi r = lo r'
        have hseam : fam.lo r' = fam.hi r := by
          rcases roots_interval_disjoint fam hr hr' (fun h => hrr h.symm) with hd | hd
          · -- hi r ≤ lo r'; with lo r' < hi r + 1 ⇒ lo r' = hi r
            omega
          · -- hi r' ≤ lo r; but hi r + 1 ≤ hi r' and lo r < t ≤ hi r ⇒ contra
            omega
        have hih := ih (b - (fam.hi r + 1)) (by omega) (fam.hi r + 1) rfl hsucc1 hsucc2
          r' hr' hr'lo hr'hi
        have hbseam := fam.bSeam r (root_self_props fam hr).1 r'
          (root_self_props fam hr').1 hseam.symm
        omega
  -- conclude for every root
  intro r hr
  obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
  have hlhr := fam.lh r hrE
  -- r does not span g
  have hnospan : ¬ (fam.lo r < g ∧ g ≤ fam.hi r) := hgap r hr
  rcases Nat.lt_or_ge (fam.hi r) g with hcase | hcase
  · -- left root: covers hi r ∈ (a, g)
    have h := scanLeft (fam.hi r) (by omega) hcase r hr (by omega) (le_refl _)
    omega
  · -- g ≤ hi r; since not span, g ≤ lo r; right root: covers lo r + 1 ∈ (g, b]
    have hglo : g ≤ fam.lo r := by
      by_contra hc; push Not at hc; exact hnospan ⟨hc, hcase⟩
    have h := scanRight (b - (fam.lo r + 1)) (fam.lo r + 1) rfl (by omega) (by omega) r hr
      (by omega) (by omega)
    omega

/-- **DIRECTIONAL COLUMN-SEPARATION (abstract).**  As `column_sep`, but exposes the gap `g`
    together with the run-direction columns: left roots (top below the gap) have `col e0 < col r`,
    right roots (bottom above the gap) have `col r < col e0`. -/
lemma column_sep_with_gap {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    {e0 : ι} (he0E : e0 ∈ fam.E) (he0lo : fam.lo e0 = a) (he0hi : fam.hi e0 = b) :
    ∃ g, a < g ∧ g ≤ b ∧ (∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r)) ∧
      (∀ r ∈ Roots fam a b, fam.hi r < g → fam.col e0 < fam.col r) ∧
      (∀ r ∈ Roots fam a b, g ≤ fam.lo r → fam.col r < fam.col e0) := by
  have htop : (topEdges fam a b).Nonempty := by
    refine ⟨e0, ?_⟩
    unfold topEdges; rw [Finset.mem_filter, mem_contained]
    exact ⟨⟨he0E, by omega, by omega⟩, he0lo, he0hi⟩
  obtain ⟨g, hg1, hg2, hgap⟩ := exists_gap fam hab hsat htop
  -- LEFT SCAN (copied from column_sep).
  have scanLeft : ∀ t, a < t → t < g → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col e0 < fam.col r := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      have hrhig : fam.hi r < g := by
        by_contra hc
        push Not at hc
        exact hgap r hr ⟨by omega, hc⟩
      by_cases hlo : fam.lo r = a
      · have hbl := fam.bLeft e0 he0E r hrE (by rw [he0lo, hlo]) (by rw [he0hi]; omega)
        exact hbl
      · have hloa : a < fam.lo r := by omega
        have hlog : fam.lo r < g := by omega
        have hlone : fam.lo r ≠ g := by omega
        obtain ⟨r'', hr'', hr''lo, hr''hi⟩ :=
          covered_of_ne_gap fam htop hsat hab hg1 hg2 hgap hloa (by omega) hlone
        have hrr : r'' ≠ r := by
          intro h; rw [h] at hr''hi hr''lo; omega
        have hseam : fam.hi r'' = fam.lo r :=
          seam_of_adjacent fam hr'' hr hr''lo hr''hi (by omega) rfl
        have hih := ih (fam.lo r) (by omega) hloa hlog r'' hr'' hr''lo hr''hi
        have hbseam := fam.bSeam r'' (root_self_props fam hr'').1 r hrE hseam
        omega
  -- RIGHT SCAN (copied from column_sep).
  have scanRight : ∀ n t, b - t = n → g < t → t ≤ b → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col r < fam.col e0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t hn ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      by_cases hhi : fam.hi r = b
      · have hbr := fam.bRight e0 he0E r hrE (by rw [he0hi, hhi]) (by rw [he0lo]; omega)
        exact hbr
      · have hhib : fam.hi r < b := by omega
        have hsucc1 : g < fam.hi r + 1 := by omega
        have hsucc2 : fam.hi r + 1 ≤ b := by omega
        have hsuccne : fam.hi r + 1 ≠ g := by omega
        obtain ⟨r', hr', hr'lo, hr'hi⟩ :=
          covered_of_ne_gap fam htop hsat hab hg1 hg2 hgap (by omega) hsucc2 hsuccne
        have hrr : r' ≠ r := by
          intro h; rw [h] at hr'lo hr'hi; omega
        have hseam : fam.lo r' = fam.hi r := by
          rcases roots_interval_disjoint fam hr hr' (fun h => hrr h.symm) with hd | hd
          · omega
          · omega
        have hih := ih (b - (fam.hi r + 1)) (by omega) (fam.hi r + 1) rfl hsucc1 hsucc2
          r' hr' hr'lo hr'hi
        have hbseam := fam.bSeam r (root_self_props fam hr).1 r'
          (root_self_props fam hr').1 hseam.symm
        omega
  refine ⟨g, hg1, hg2, hgap, ?_, ?_⟩
  · intro r hr hrg
    obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
    have hlhr := fam.lh r hrE
    exact scanLeft (fam.hi r) (by omega) hrg r hr (by omega) (le_refl _)
  · intro r hr hgr
    obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
    have hlhr := fam.lh r hrE
    exact scanRight (b - (fam.lo r + 1)) (fam.lo r + 1) rfl (by omega) (by omega) r hr
      (by omega) (by omega)


end AbstractLaminar

/-! ## PART B — geometric layer in `CriticalPortraits`. -/

namespace CriticalPortraits

open Finset
open scoped BigOperators

variable {d m : ℕ}

/-! ### B0. blocks = host sets: `P = image (survivor ↦ hostSet)`. -/

/-- Each block of a portrait is the host set of any of its survivors.  More precisely: if
    `x ∈ eraseMin S` and `S ∈ P` then `hostSet P x = S` (the survivor's recovered home is its
    block, by portrait disjointness). -/
lemma hostSet_eq_of_mem_eraseMin {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {S : Finset (ZMod (d * m))} (hS : S ∈ P) {x : ZMod (d * m)} (hxe : x ∈ eraseMin S) :
    hostSet P x (mem_T.mpr ⟨S, hS, hxe⟩) = S := by
  set hx : x ∈ T P := mem_T.mpr ⟨S, hS, hxe⟩ with hhx
  by_contra hne
  -- both S and hostSet P x hx contain x; if distinct they are disjoint — contradiction.
  have hhost : hostSet P x hx ∈ P := hostSet_mem hx
  have hxS : x ∈ S := eraseMin_subset S hxe
  have hxH : x ∈ hostSet P x hx := mem_hostSet hx
  have hdisj := hP.2.1 _ hhost _ hS (by exact fun h => hne h)
  exact (Finset.disjoint_left.mp hdisj hxH) hxS

/-- **`P` is recovered as the image of its survivors' host sets.** -/
lemma portrait_eq_image_hostSet {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    P = (T P).attach.image (fun x => hostSet P x.1 x.2) := by
  apply Finset.ext
  intro S
  constructor
  · -- S ∈ P ⇒ S is some hostSet
    intro hS
    -- S has a survivor (card ≥ 2 ⇒ eraseMin nonempty)
    have hcard : 2 ≤ S.card := (hP.1 S hS).2
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hecard : (eraseMin S).card = S.card - 1 := eraseMin_card S hSne
    have hene : (eraseMin S).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxe⟩ := hene
    have hx : x ∈ T P := mem_T.mpr ⟨S, hS, hxe⟩
    rw [Finset.mem_image]
    refine ⟨⟨x, hx⟩, Finset.mem_attach _ _, ?_⟩
    exact hostSet_eq_of_mem_eraseMin hP hS hxe
  · -- image element ⇒ in P
    intro hS
    rw [Finset.mem_image] at hS
    obtain ⟨x, _, hxeq⟩ := hS
    rw [← hxeq]
    exact hostSet_mem x.2

/-! ### B1. Geometric TIGHTNESS and COLUMN-SEPARATION for the survivor family.

We instantiate the abstract TIGHTNESS at the real `survivorFamily`.  The window `(0, d-1]`
is saturated (`N = d-1`) because every survivor's level lies in `[0, d-1]` — `0 ≤ loV` and
`hiV ≤ d-1`, so all `d-1` edges are contained, and the window width is `d-1`. -/

/-- Every survivor's level is `< d` (hence `hiV x ≤ d - 1`). -/
lemma hiV_lt_d [NeZero (d * m)] (_hm : 0 < m) (x : ZMod (d * m)) : hiV x < d := by
  unfold hiV
  have hval : x.val < d * m := ZMod.val_lt x
  have hval' : x.val < m * d := lt_of_lt_of_le hval (le_of_eq (Nat.mul_comm d m))
  exact Nat.div_lt_of_lt_mul hval'

/-- The window `(0, d-1]` contains every edge of the survivor family. -/
lemma survivorFamily_contained_eq [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    AbstractLaminar.contained (survivorFamily hd hm hP) 0 (d - 1) = T P := by
  unfold AbstractLaminar.contained
  apply Finset.filter_true_of_mem
  intro e he
  refine ⟨Nat.zero_le _, ?_⟩
  -- hi e = hiV e ≤ d - 1
  change hiV e ≤ d - 1
  have := hiV_lt_d (d := d) (m := m) hm e
  omega

/-- **Geometric saturation.** `N (survivorFamily) 0 (d-1) = d - 1`. -/
lemma survivorFamily_saturated [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    AbstractLaminar.N (survivorFamily hd hm hP) 0 (d - 1) = (d - 1) - 0 := by
  unfold AbstractLaminar.N
  rw [survivorFamily_contained_eq hd hm hP, T_card hP]
  omega

/-- **Geometric TIGHTNESS (g(e) = h(e) - 1).** Every survivor edge `e` has a saturated own
    window: `N(loV e, hiV e) = hiV e - loV e`. -/
theorem edge_tight_geom [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e : ZMod (d * m)} (he : e ∈ T P) :
    AbstractLaminar.N (survivorFamily hd hm hP) (loV P e) (hiV e)
      = hiV e - loV P e := by
  set fam := survivorFamily hd hm hP with hfam
  have hsat := survivorFamily_saturated hd hm hP
  have hcont : e ∈ AbstractLaminar.contained fam 0 (d - 1) := by
    rw [survivorFamily_contained_eq hd hm hP]; exact he
  have := AbstractLaminar.edge_tight_of_saturated fam (d - 1 - 0) 0 (d - 1) rfl hsat e hcont
  exact this

/-- **Geometric COLUMN-SEPARATION.** For a survivor edge `e` with a nondegenerate own window,
    every maximal nested tile (root of `(loV e, hiV e]`) has column `≠ colV e`. -/
theorem column_sep_geom [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e : ZMod (d * m)} (he : e ∈ T P) (hwin : loV P e < hiV e) :
    ∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
      colV r ≠ colV e := by
  set fam := survivorFamily hd hm hP with hfam
  have hsat := edge_tight_geom hd hm hP he
  -- `e` itself is the top edge of window (loV e, hiV e].
  have heE : e ∈ fam.E := he
  exact AbstractLaminar.column_sep fam hwin hsat heE rfl rfl

/-- **Geometric DIRECTIONAL COLUMN-SEPARATION.**  Exposes the gap level and the run-direction
    columns at the survivor family. -/
theorem column_sep_geom_dir [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e : ZMod (d * m)} (he : e ∈ T P) (hwin : loV P e < hiV e) :
    ∃ g, loV P e < g ∧ g ≤ hiV e ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        ¬ (loV P r < g ∧ g ≤ hiV r)) ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        hiV r < g → colV e < colV r) ∧
      (∀ r ∈ AbstractLaminar.Roots (survivorFamily hd hm hP) (loV P e) (hiV e),
        g ≤ loV P r → colV r < colV e) := by
  set fam := survivorFamily hd hm hP with hfam
  have hsat := edge_tight_geom hd hm hP he
  have heE : e ∈ fam.E := he
  exact AbstractLaminar.column_sep_with_gap fam hwin hsat heE rfl rfl

/-! ### B2. Block spans and Lemma 2 (span laminarity).

`spanLo S`, `spanHi S` are the `.val` of the lowest/highest points of a block `S`.  Lemma 2
says distinct blocks' spans are laminar (nested or disjoint), proved directly from `Unlinked`
+ the alternation witness `linked_of_lt` (structurally identical to `lemmaA`/`cross_false`). -/

/-- The greatest-`.val` element of a nonempty set. -/
noncomputable def maxVal {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ZMod N :=
  (Finset.exists_max_image S (fun x => x.val) h).choose

lemma maxVal_mem {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : maxVal S h ∈ S :=
  (Finset.exists_max_image S (fun x => x.val) h).choose_spec.1

lemma maxVal_ge {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) :
    ∀ x ∈ S, x.val ≤ (maxVal S h).val :=
  (Finset.exists_max_image S (fun x => x.val) h).choose_spec.2

/-- The `.val`-span of a block: `[minVal, maxVal]`. -/
noncomputable def spanLo {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ℕ := (minVal S h).val
/-- The greatest `.val` attained on a nonempty finset `S`. -/
noncomputable def spanHi {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ℕ := (maxVal S h).val

/-- **Lemma 2 (span laminarity).** Distinct blocks of a portrait have laminar spans: nested or
    disjoint (no proper `.val`-overlap `spanLo A < spanLo B < spanHi A < spanHi B`). -/
theorem span_laminar {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {A B : Finset (ZMod (d * m))} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ¬ (spanLo A hAne < spanLo B hBne ∧ spanLo B hBne < spanHi A hAne ∧
       spanHi A hAne < spanHi B hBne) := by
  rintro ⟨h1, h2, h3⟩
  -- the four endpoints minVal A < minVal B < maxVal A < maxVal B alternate ⇒ Linked A B
  simp only [spanLo, spanHi] at h1 h2 h3
  have hL : Linked A B :=
    linked_of_lt (minVal_mem A hAne) (maxVal_mem A hAne) (minVal_mem B hBne) (maxVal_mem B hBne)
      h1 h2 h3
  exact (hP.2.2.1 A hA B hB hAB) hL

/-- **Lemma 2 (hull edge).** Every block element's `.val` lies within the span. -/
lemma mem_span {N : ℕ} {S : Finset (ZMod N)} (h : S.Nonempty) {x : ZMod N} (hx : x ∈ S) :
    spanLo S h ≤ x.val ∧ x.val ≤ spanHi S h :=
  ⟨minVal_le S h x hx, maxVal_ge S h x hx⟩

/-! ### B3. The BRIDGE (edge core).

The algebraic heart of the Structural Lemma: a same-column edge strictly nested inside `u`'s edge
is NOT a maximal tile (its `rootS` is a strictly-enclosing edge of a DIFFERENT column).  This is
exactly "the c*-block `B` strictly inside `(w,u)` is enclosed by an in-gap block of column ≠ c*",
phrased in the edge model.  Proved from `column_sep_geom` + the rootS machinery. -/

/-- **BRIDGE (edge form).** If a survivor `b2` (same column as `u`) has its edge strictly nested
    inside `u`'s edge, then there is a survivor `g` of a DIFFERENT column whose edge encloses
    `b2`'s and is nested in `u`'s: `loV u ≤ loV g ≤ loV b2`, `hiV b2 ≤ hiV g ≤ hiV u`,
    `colV g ≠ colV u`, and `g ≠ b2`. -/
theorem bridge_edge [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u b2 : ZMod (d * m)} (hu : u ∈ T P) (hb2 : b2 ∈ T P)
    (hcol : colV b2 = colV u)
    (hlo : loV P u < loV P b2) (hhi : hiV b2 < hiV u) :
    ∃ g ∈ T P, colV g ≠ colV u ∧
      loV P u ≤ loV P g ∧ loV P g ≤ loV P b2 ∧ hiV b2 ≤ hiV g ∧ hiV g ≤ hiV u ∧ g ≠ b2 := by
  set fam := survivorFamily hd hm hP with hfam
  -- window of u's edge
  have hwin : loV P u < hiV u := by
    change fam.lo u < fam.hi u; exact fam.lh u hu
  -- b2 ∈ Sstrict of u's window (strictly nested: lo ≠ loV u OR hi ≠ hiV u — both hold)
  have hb2cont : b2 ∈ AbstractLaminar.contained fam (loV P u) (hiV u) := by
    rw [AbstractLaminar.mem_contained]
    refine ⟨hb2, by change loV P u ≤ loV P b2; omega, by change hiV b2 ≤ hiV u; omega⟩
  have hb2S : b2 ∈ AbstractLaminar.Sstrict fam (loV P u) (hiV u) := by
    rw [AbstractLaminar.mem_Sstrict]
    refine ⟨⟨hb2, by change loV P u ≤ loV P b2; omega, by change hiV b2 ≤ hiV u; omega⟩, ?_⟩
    left; change loV P b2 ≠ loV P u; omega
  -- g := rootS of b2 in u's window
  set g := AbstractLaminar.rootS fam (loV P u) (hiV u) b2 with hg
  have hgRoot : g ∈ AbstractLaminar.Roots fam (loV P u) (hiV u) :=
    AbstractLaminar.rootS_mem_Roots fam hb2S
  have hgE : g ∈ T P := AbstractLaminar.rootS_mem_E fam hb2S
  have hgwin := AbstractLaminar.rootS_window fam hb2S
  have hgcont := AbstractLaminar.rootS_contains fam hb2S
  -- column separation: col g ≠ col u
  have hgcol : colV g ≠ colV u := column_sep_geom hd hm hP hu hwin g hgRoot
  -- g ≠ b2 : equal edges (same col impossible since col g ≠ col u = col b2)
  have hgb2 : g ≠ b2 := by
    intro h; rw [h] at hgcol; exact hgcol hcol
  refine ⟨g, hgE, hgcol, ?_, ?_, ?_, ?_, hgb2⟩
  · exact hgwin.1
  · exact hgcont.1
  · exact hgcont.2
  · exact hgwin.2

/-! ### B-keystone (stage 1): the predecessor of each survivor is FORCED by `U = T P`.

This is the genuinely deep all-`d` kernel — the inductive forced-predecessor dispatch that
consumes the now-proved `bridge_edge` / `column_sep_geom` / `edge_tight_geom` / `span_laminar`.
It is now PROVED (no `sorry`); the stage-2 component recovery `hostSet_forced` below
depends on it. -/

/- **KEYSTONE (stage 1).**

If two portraits share their survivor set `U`, each survivor's immediate predecessor agrees.

Paper argument (Part I): `w = predIn P u` is the greedy maximal-`.val` same-fiber candidate
`v < u` whose chord `(v,u)` is legal (`v ∉ U` as a committed top, and `(v,u)` crosses no
already-committed lower edge).  The legality test references only `U` and lower (forced) edges, so
`predIn` is a function of `U`.  Every higher candidate `v ∈ (w,u)` is illegal: used (`v ∈ U`), or
its maximal column-`c*` block is — by the **Structural Lemma / Bridge** (`bridge_edge`) — strictly
enclosed by an in-gap block of a different column whose edge `(a,b)` crosses `(v,u)`.

Available sorry-free substrate consumed by the missing proof: `edge_tight_geom` (TIGHTNESS),
`column_sep_geom` (COLUMN-SEP), `bridge_edge` (BRIDGE edge core), `span_laminar` (Lemma 2),
plus Forward's `predIn_immediate` / `no_alt` / `predIn_max`. -/

/-! #### Helper lemmas for `predIn_forced`. -/

/-- Same-fiber `.val` comparison is the level comparison (strict). -/
lemma level_lt_of_val_lt [NeZero (d * m)] {x y : ZMod (d * m)}
    (hfib : x.val % m = y.val % m) (h : x.val < y.val) : x.val / m < y.val / m := by
  rcases lt_or_eq_of_le ((val_le_iff_level_le_of_sameFiber hfib).mp h.le) with hlt | heq
  · exact hlt
  · exact absurd (congrArg ZMod.val (level_injOn_fiber hfib heq)) (Nat.ne_of_lt h)

/-- A strict root `g` of `x`'s window (so `loV P x ≤ loV P g`, `hiV g ≤ hiV x`,
    `colV g ≠ colV x`) has `g.val < x.val`. -/
lemma root_val_lt [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {g x : ZMod (d * m)} (hg : g ∈ T P) (hx : x ∈ T P)
    (hlo : loV P x ≤ loV P g) (hhi : hiV g ≤ hiV x) (hcol : colV g ≠ colV x) : g.val < x.val := by
  have hgv := top_val_eq (x := g)
  have hxv := top_val_eq (x := x)
  rcases lt_or_eq_of_le hhi with hlt | heq
  · have := sep_master (m := m) (p := colV g) (q := colV x) (colV_lt_m hm g) (colV_lt_m hm x) hlt
    omega
  · -- hiV g = hiV x.  Then loV P x < loV P g (else equal edges → g = x → colV g = colV x).
    have hlostrict : loV P x < loV P g := by
      rcases lt_or_eq_of_le hlo with h | h
      · exact h
      · exact absurd (edge_inj hd hm hP hx hg h heq.symm) (fun hxg => hcol (by rw [hxg]))
    have hcg : colV g < colV x := lemmaB_right hd hm hP hx hg heq.symm hlostrict
    have : colV g + hiV g * m < colV x + hiV x * m := by rw [heq]; omega
    omega

/-- **The spanning-edge kernel.**  In one portrait `P`, for a survivor `x` and a level `ℓ`
    strictly inside `x`'s own window `(loV P x, hiV x)`, there is a survivor `b` of a different
    column than `x` whose edge **straddles** the value `colV x + ℓ * m`:
    `(predIn P b _).val < colV x + ℓ*m < b.val < x.val`.

    This is the formalized **Structural Lemma / Bridge** content: the value `v₀ = colV x + ℓ*m`
    (a same-fiber position strictly inside `x`'s edge) is crossed by some maximal nested tile of a
    different column.  Proved from saturation (`edge_tight_geom`), column-separation
    (`column_sep_geom`), and the gap/cover/seam machinery. -/
lemma spanning_edge [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) {x : ZMod (d * m)} (hx : x ∈ T P)
    {ℓ : ℕ} (hℓ1 : loV P x < ℓ) (hℓ2 : ℓ < hiV x) :
    ∃ b, ∃ hb : b ∈ T P, colV b ≠ colV x ∧
      (predIn P b hb).val < colV x + ℓ * m ∧ colV x + ℓ * m < b.val ∧ b.val < x.val := by
  set fam := survivorFamily hd hm hP with hfam
  have hwin : loV P x < hiV x := by change fam.lo x < fam.hi x; exact fam.lh x hx
  have hsat : AbstractLaminar.N fam (loV P x) (hiV x) = hiV x - loV P x :=
    edge_tight_geom hd hm hP hx
  have htop : (AbstractLaminar.topEdges fam (loV P x) (hiV x)).Nonempty := by
    refine ⟨x, ?_⟩
    unfold AbstractLaminar.topEdges
    rw [Finset.mem_filter, AbstractLaminar.mem_contained]
    exact ⟨⟨hx, le_refl _, le_refl _⟩, rfl, rfl⟩
  have hcx := colV_lt_m hm x
  -- gap + directional column facts.
  obtain ⟨gp, hgp1, hgp2, hgpgap, hleft, hright⟩ := column_sep_geom_dir hd hm hP hx hwin
  -- a generic finisher: given a root r covering value v₀ = colV x + ℓ*m in its arc, finish.
  -- We split on ℓ < gp (use the tile covering ℓ) vs ℓ ≥ gp (use the tile covering ℓ+1).
  rcases Nat.lt_or_ge ℓ gp with hlg | hge
  · -- ℓ < gp : the root covering level ℓ straddles v₀.
    obtain ⟨r, hr, hrlo0, hrhi0⟩ :=
      AbstractLaminar.covered_of_ne_gap fam htop hsat hwin hgp1 hgp2 hgpgap
        (show loV P x < ℓ from hℓ1) (le_of_lt hℓ2) (by omega : ℓ ≠ gp)
    have hrlo : loV P r < ℓ := hrlo0
    have hrhi : ℓ ≤ hiV r := hrhi0
    obtain ⟨hrE, hra0, hrb0, _⟩ := AbstractLaminar.root_self_props fam hr
    have hra : loV P x ≤ loV P r := hra0
    have hrb : hiV r ≤ hiV x := hrb0
    have hcolne : colV r ≠ colV x := column_sep_geom hd hm hP hx hwin r hr
    have hgpgap' : ¬ (loV P r < gp ∧ gp ≤ hiV r) := hgpgap r hr
    have hrhig : hiV r < gp := by
      by_contra hc; push Not at hc; exact hgpgap' ⟨by omega, hc⟩
    have hcolxr : colV x < colV r := hleft r hr hrhig
    have hcr := colV_lt_m hm r
    have hpr : (predIn P r hrE).val = colV r + loV P r * m := pred_val_eq hP hrE
    have hrv : r.val = colV r + hiV r * m := top_val_eq (x := r)
    refine ⟨r, hrE, hcolne, ?_, ?_, ?_⟩
    · have := sep_master (m := m) (p := colV r) (q := colV x) hcr hcx hrlo
      rw [hpr]; omega
    · rcases lt_or_eq_of_le hrhi with hlt | heq
      · have := sep_master (m := m) (p := colV x) (q := colV r) hcx hcr hlt
        rw [hrv]; omega
      · rw [hrv, ← heq]; omega
    · exact root_val_lt hd hm hP hrE hx hra hrb hcolne
  · -- ℓ ≥ gp : the root covering level ℓ+1 straddles v₀.
    have hℓ1' : loV P x < ℓ + 1 := by omega
    have hℓ2' : ℓ + 1 ≤ hiV x := by omega
    have hne' : ℓ + 1 ≠ gp := by omega
    obtain ⟨r, hr, hrlo0, hrhi0⟩ :=
      AbstractLaminar.covered_of_ne_gap fam htop hsat hwin hgp1 hgp2 hgpgap hℓ1' hℓ2' hne'
    have hrlo : loV P r < ℓ + 1 := hrlo0
    have hrhi : ℓ + 1 ≤ hiV r := hrhi0
    obtain ⟨hrE, hra0, hrb0, _⟩ := AbstractLaminar.root_self_props fam hr
    have hra : loV P x ≤ loV P r := hra0
    have hrb : hiV r ≤ hiV x := hrb0
    have hcolne : colV r ≠ colV x := column_sep_geom hd hm hP hx hwin r hr
    have hrlo' : loV P r ≤ ℓ := by omega
    have hgpgap' : ¬ (loV P r < gp ∧ gp ≤ hiV r) := hgpgap r hr
    have hgr : gp ≤ loV P r := by
      by_contra hc; push Not at hc; exact hgpgap' ⟨hc, by omega⟩
    have hcolrx : colV r < colV x := hright r hr hgr
    have hcr := colV_lt_m hm r
    have hpr : (predIn P r hrE).val = colV r + loV P r * m := pred_val_eq hP hrE
    have hrv : r.val = colV r + hiV r * m := top_val_eq (x := r)
    refine ⟨r, hrE, hcolne, ?_, ?_, ?_⟩
    · rcases lt_or_eq_of_le hrlo' with hlt | heq
      · have := sep_master (m := m) (p := colV r) (q := colV x) hcr hcx hlt
        rw [hpr]; omega
      · rw [hpr, heq]; omega
    · have := sep_master (m := m) (p := colV x) (q := colV r) hcx hcr (show ℓ < hiV r by omega)
      rw [hrv]; omega
    · exact root_val_lt hd hm hP hrE hx hra hrb hcolne

theorem predIn_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {x : ZMod (d * m)} (hx₁ : x ∈ T P₁) (hx₂ : x ∈ T P₂) :
    predIn P₁ x hx₁ = predIn P₂ x hx₂ := by
  induction hn : x.val using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  subst hn
  -- IH: equality for strictly-lower survivors.
  have IH : ∀ y : ZMod (d*m), y.val < x.val → ∀ (hy₁ : y ∈ T P₁) (hy₂ : y ∈ T P₂),
      predIn P₁ y hy₁ = predIn P₂ y hy₂ := by
    intro y hyv hy₁ hy₂
    exact ih y.val hyv hy₁ hy₂ rfl
  -- one-directional WLOG, generic in the ordered pair of portraits.
  have noLt : ∀ (Q₁ Q₂ : Finset (Finset (ZMod (d*m)))), Portrait d m Q₁ → Portrait d m Q₂ →
      T Q₁ = T Q₂ → (∀ y : ZMod (d*m), y.val < x.val → ∀ (hy₁ : y ∈ T Q₁) (hy₂ : y ∈ T Q₂),
        predIn Q₁ y hy₁ = predIn Q₂ y hy₂) →
      ∀ (hq₁ : x ∈ T Q₁) (hq₂ : x ∈ T Q₂),
        ¬ ((predIn Q₁ x hq₁).val < (predIn Q₂ x hq₂).val) := by
    intro Q₁ Q₂ hQ₁ hQ₂ hTQ IHQ hq₁ hq₂ hlt
    set w₁ := predIn Q₁ x hq₁ with hw₁
    set w₂ := predIn Q₂ x hq₂ with hw₂
    have hfib₁ : w₁.val % m = x.val % m := predIn_sameFiber hQ₁ hq₁
    have hfib₂ : w₂.val % m = x.val % m := predIn_sameFiber hQ₂ hq₂
    have hfib12 : w₁.val % m = w₂.val % m := by rw [hfib₁, hfib₂]
    have hw1lt : w₁.val < x.val := predIn_val_lt hq₁
    have hw2lt : w₂.val < x.val := predIn_val_lt hq₂
    have hcolw₂x : colV w₂ = colV x := by unfold colV; rw [hfib₂]
    -- levels
    have hlevel_w1 : loV Q₁ x = w₁.val / m := loV_eq hq₁
    have hlevel_w2 : loV Q₂ x = w₂.val / m := loV_eq hq₂
    set ℓ := w₂.val / m with hℓdef
    have hℓ_eq_lo2 : loV Q₂ x = ℓ := by rw [hlevel_w2]
    have hlt_lev_12 : w₁.val / m < ℓ := level_lt_of_val_lt hfib12 hlt
    have hℓ_gt_lo1 : loV Q₁ x < ℓ := by rw [hlevel_w1]; exact hlt_lev_12
    have hℓ_lt_hi : ℓ < hiV x := by
      have := level_lt_of_val_lt hfib₂ hw2lt
      simpa [hℓdef, hiV] using this
    have hw2val : w₂.val = colV x + ℓ * m := by
      have h := top_val_eq (x := w₂)
      rw [hcolw₂x] at h
      have hhi : hiV w₂ = ℓ := rfl
      rw [hhi] at h; exact h
    -- The spanning edge over v₀ = colV x + ℓ*m, in Q₁.
    obtain ⟨b, hb₁, hbcol, hbpred, hbgt, hblt⟩ :=
      spanning_edge hd hm hQ₁ hq₁ hℓ_gt_lo1 hℓ_lt_hi
    -- transfer b's edge to Q₂ via IH.
    have hb₂ : b ∈ T Q₂ := hTQ ▸ hb₁
    have hbforce : predIn Q₁ b hb₁ = predIn Q₂ b hb₂ := IHQ b hblt hb₁ hb₂
    -- the crossing in Q₂: predIn b < w₂ < b < x.
    have o1 : (predIn Q₂ b hb₂).val < w₂.val := by
      rw [← hbforce, hw2val]; exact hbpred
    have o2 : w₂.val < b.val := by rw [hw2val]; exact hbgt
    have o3 : b.val < x.val := hblt
    exact no_alt hQ₂ hb₂ hq₂ o1 o2 o3
  have h12 := noLt P₁ P₂ h₁ h₂ hT IH hx₁ hx₂
  have h21 := noLt P₂ P₁ h₂ h₁ hT.symm (fun y hyv hy₂ hy₁ => (IH y hyv hy₁ hy₂).symm) hx₂ hx₁
  exact ZMod.val_injective _ (le_antisymm (not_lt.mp h21) (not_lt.mp h12))

/-! ### B-keystone (stage 2): host blocks are forced by `U` and the forced predecessors.

Stage 2 is sorry-free.  A block is recovered as the connected component of its survivors under
the immediate-predecessor (`edgeStep`) relation, together with its unique non-survivor `minVal`
(the "root").  Since `T P` and (by `predIn_forced`) the `predIn` map agree across `P₁, P₂`, the
`edgeStep` relation agrees, hence components and roots agree, hence host blocks agree. -/

/-- `hostSet P u` is THE block containing the survivor `u`. -/
lemma hostSet_eq_of_mem {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u : ZMod (d * m)} (hu : u ∈ T P) {S : Finset (ZMod (d * m))} (hSP : S ∈ P) (huS : u ∈ S) :
    hostSet P u hu = S := by
  by_contra hne
  exact (Finset.disjoint_left.mp (hP.2.1 _ (hostSet_mem hu) _ hSP hne) (mem_hostSet hu)) huS

/-- `minVal` only depends on the set (proof-irrelevant nonemptiness witness). -/
lemma minVal_congr {N : ℕ} {S S' : Finset (ZMod N)} (hS : S.Nonempty) (hS' : S'.Nonempty)
    (h : S = S') : minVal S hS = minVal S' hS' := by subst h; rfl

/-- The dropped point of a block is not a survivor of `P` (blocks are disjoint). -/
lemma minVal_host_not_mem_T {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x : ZMod (d * m)} (hx : x ∈ T P) (hne : (hostSet P x hx).Nonempty) :
    minVal (hostSet P x hx) hne ∉ T P := by
  intro hmem
  set S := hostSet P x hx with hSdef
  set w := minVal S hne with hwdef
  have hSP : S ∈ P := hostSet_mem hx
  have hwS : w ∈ S := minVal_mem S hne
  obtain ⟨S', hS'P, hwS'⟩ := mem_T.mp hmem
  have hwS'S : w ∈ S' := eraseMin_subset S' hwS'
  have hSS' : S = S' := by
    by_contra hne'
    exact (Finset.disjoint_left.mp (hP.2.1 _ hSP _ hS'P hne') hwS) hwS'S
  rw [← hSS'] at hwS'
  exact ((mem_eraseMin S hne w).mp hwS').2 rfl

/-- The same-block immediate-predecessor step relation on survivors:
    determined by `T P` + `predIn`. -/
def edgeStep [NeZero (d * m)] (P : Finset (Finset (ZMod (d * m)))) (u v : ZMod (d * m)) : Prop :=
  ∃ (hu : u ∈ T P) (hv : v ∈ T P), predIn P u hu = v ∨ predIn P v hv = u

lemma edgeStep_symm [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))}
    {u v : ZMod (d * m)} (h : edgeStep P u v) : edgeStep P v u := by
  obtain ⟨hu, hv, hcase⟩ := h; exact ⟨hv, hu, hcase.symm⟩

lemma reach_symm [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))}
    {u v : ZMod (d * m)} (h : Relation.ReflTransGen (edgeStep P) u v) :
    Relation.ReflTransGen (edgeStep P) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact Relation.ReflTransGen.head (edgeStep_symm hbc) ih

/-- An `edgeStep` keeps you in the same host (the predecessor lives in the same block). -/
lemma edgeStep_sameHost [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u v : ZMod (d * m)} (hstep : edgeStep P u v) (hu : u ∈ T P) (hv : v ∈ T P) :
    hostSet P u hu = hostSet P v hv := by
  obtain ⟨hu', hv', hcase⟩ := hstep
  rcases hcase with hpu | hpv
  · have : v ∈ hostSet P u hu := by rw [← hpu]; exact predIn_mem_host hu
    exact (hostSet_eq_of_mem hP hv (hostSet_mem hu) this).symm
  · have : u ∈ hostSet P v hv := by rw [← hpv]; exact predIn_mem_host hv
    exact hostSet_eq_of_mem hP hu (hostSet_mem hv) this

/-- For a survivor `u` whose predecessor is itself a survivor, they share a host. -/
lemma hostSet_predIn [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u : ZMod (d * m)} (hu : u ∈ T P) (hpu : predIn P u hu ∈ T P) :
    hostSet P (predIn P u hu) hpu = hostSet P u hu :=
  hostSet_eq_of_mem hP hpu (hostSet_mem hu) (predIn_mem_host hu)

/-- Survivors reachable from `x` by `edgeStep` share `x`'s host. -/
lemma reach_sameHost [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x z : ZMod (d * m)} (hx : x ∈ T P)
    (hreach : Relation.ReflTransGen (edgeStep P) x z) (hz : z ∈ T P) :
    hostSet P z hz = hostSet P x hx := by
  induction hreach with
  | refl => rfl
  | @tail b c hxb hbc ih =>
    obtain ⟨hb, hc', hcase⟩ := hbc
    have hbc_host : hostSet P b hb = hostSet P c hc' :=
      edgeStep_sameHost hP ⟨hb, hc', hcase⟩ hb hc'
    have hzc : hostSet P c hz = hostSet P c hc' := rfl
    rw [hzc, ← hbc_host]; exact ih hb

/-- Every survivor `z` reaches the bottom survivor `q` of its block (predecessor a non-survivor). -/
lemma reach_to_low [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    ∀ n : ℕ, ∀ z : ZMod (d*m), z.val = n → (hz : z ∈ T P) →
      ∃ q, ∃ hq : q ∈ T P, predIn P q hq ∉ T P ∧
        hostSet P q hq = hostSet P z hz ∧ Relation.ReflTransGen (edgeStep P) z q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hzn hz
    set p := predIn P z hz with hpdef
    by_cases hpT : p ∈ T P
    · have hpval : p.val < z.val := predIn_val_lt hz
      obtain ⟨q, hq, hqpred, hqhost, hqreach⟩ := ih p.val (by omega) p rfl hpT
      exact ⟨q, hq, hqpred, by rw [hqhost, hostSet_predIn hP hz hpT],
        Relation.ReflTransGen.head ⟨hz, hpT, Or.inl rfl⟩ hqreach⟩
    · exact ⟨z, hz, hpT, rfl, Relation.ReflTransGen.refl⟩

/-- Two survivors in the same host reach the SAME bottom survivor; hence are mutually reachable. -/
lemma reach_of_sameHost [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x z : ZMod (d * m)} (hx : x ∈ T P) (hz : z ∈ T P)
    (hhost : hostSet P z hz = hostSet P x hx) :
    Relation.ReflTransGen (edgeStep P) z x := by
  obtain ⟨qz, hqz, hqzpred, hqzhost, hqzreach⟩ := reach_to_low hP z.val z rfl hz
  obtain ⟨qx, hqx, hqxpred, hqxhost, hqxreach⟩ := reach_to_low hP x.val x rfl hx
  have hsamehost : hostSet P qz hqz = hostSet P qx hqx := by rw [hqzhost, hqxhost, hhost]
  have hzne : (hostSet P qz hqz).Nonempty := ⟨qz, mem_hostSet hqz⟩
  have hxne : (hostSet P qx hqx).Nonempty := ⟨qx, mem_hostSet hqx⟩
  have hpqz_min : predIn P qz hqz = minVal (hostSet P qz hqz) hzne := by
    by_contra hne
    exact hqzpred (mem_T.mpr ⟨_, hostSet_mem hqz,
      (mem_eraseMin _ hzne _).mpr ⟨predIn_mem_host hqz, hne⟩⟩)
  have hpqx_min : predIn P qx hqx = minVal (hostSet P qx hqx) hxne := by
    by_contra hne
    exact hqxpred (mem_T.mpr ⟨_, hostSet_mem hqx,
      (mem_eraseMin _ hxne _).mpr ⟨predIn_mem_host hqx, hne⟩⟩)
  have hpredeq : predIn P qz hqz = predIn P qx hqx := by
    rw [hpqz_min, hpqx_min]; exact minVal_congr hzne hxne hsamehost
  have hqeq : qz = qx := by
    by_contra hqne
    have hqzlt : (predIn P qz hqz).val < qz.val := predIn_val_lt hqz
    have hqxlt : (predIn P qx hqx).val < qx.val := predIn_val_lt hqx
    have hqxinz : qx ∈ hostSet P qz hqz := by rw [hsamehost]; exact mem_hostSet hqx
    have hqzinx : qz ∈ hostSet P qx hqx := by rw [← hsamehost]; exact mem_hostSet hqz
    rcases lt_trichotomy qz.val qx.val with hlt | heq | hgt
    · exact predIn_immediate hqx hqzinx (by rw [← hpredeq]; exact hqzlt) hlt
    · exact hqne (ZMod.val_injective _ heq)
    · exact predIn_immediate hqz hqxinz (by rw [hpredeq]; exact hqxlt) hgt
  subst hqeq
  exact hqzreach.trans (reach_symm hqxreach)

/-- With forced predecessors and equal survivor sets, the `edgeStep` relations agree. -/
lemma edgeStep_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {u v : ZMod (d * m)} (hstep : edgeStep P₁ u v) : edgeStep P₂ u v := by
  obtain ⟨hu₁, hv₁, hcase⟩ := hstep
  have hu₂ : u ∈ T P₂ := hT ▸ hu₁
  have hv₂ : v ∈ T P₂ := hT ▸ hv₁
  refine ⟨hu₂, hv₂, ?_⟩
  rcases hcase with hpu | hpv
  · left; rw [← predIn_forced hd hm h₁ h₂ hT hu₁ hu₂]; exact hpu
  · right; rw [← predIn_forced hd hm h₁ h₂ hT hv₁ hv₂]; exact hpv

/-- Reachability transfers between portraits with forced predecessors. -/
lemma reach_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {u v : ZMod (d * m)}
    (hreach : Relation.ReflTransGen (edgeStep P₁) u v) :
    Relation.ReflTransGen (edgeStep P₂) u v := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact Relation.ReflTransGen.tail ih (edgeStep_forced hd hm h₁ h₂ hT hbc)

/-! ### B-keystone: the host sets are forced by the survivor set `U = T P`.

This is exactly Part I (Uniqueness) of the paper: a critical portrait is reconstructible from
its survivor set.  All of the structural content (TIGHTNESS, Column-Separation, the Bridge /
Structural Lemma, and the resulting "predecessor forced ⇒ block forced") lives here. -/

/-- **KEYSTONE (Part I uniqueness) — now PROVED (sorry-free).**

If two portraits have the same survivor set, then each survivor's host block is the same in both.
This is exactly the paper's Part I ("`T` injective ↔ the portrait is reconstructible from `U`"),
the documented open all-`d` kernel (machine-verified `d ≤ 8`; never previously mechanized for all
`d`).  Its proof has two stages, both genuinely deep:

  (1) **`predIn` forced.**  `∀ u ∈ U, predIn P₁ u = predIn P₂ u`.  By induction over `.val` order:
      `w = predIn P u` is the GREEDY pick from `U` — the highest same-fiber `v < u` that is unused
      and whose chord `(v,u)` crosses no already-committed (lower-`.val`) edge.  Every higher
      candidate `v ∈ (w,u)` is illegal: either `v ∈ U` (a non-top of its block; its child is left
      of `u`, already committed) or, by the **Structural Lemma / Bridge**, `v`'s block is not
      maximal in `(w,u)`, so it sits in the gap of an enclosing block whose edge `(a,b)` has
      `a < v < b < u`, crossing the committed `(a,b)`.  The Structural Lemma ("no block maximal in
      a parent-gap `(w,u)` has its top in `fiber(u)`") is fed by the now-PROVED substrate:
        • TIGHTNESS  : `edge_tight_geom` (`g(e) = h(e) - 1`).
        • COLUMN-SEP : `column_sep_geom` (no maximal tile of `e` shares `e`'s column).
        • BRIDGE     : `bridge_edge` (PROVED) — the c*-edge `eB` of a c*-block `B` strictly inside
                       `(w,u)` is non-maximal, so `eB ≪` a maximal tile `g` with `col g ≠ c*`.
                       Remaining glue: `span_laminar` (Lemma 2, PROVED) + chord-enclosure
                       (`sep_master`) ⇒ `block(g)` strictly encloses `span(B)` ⇒ `B` not maximal.

  (2) **Block forced from `predIn`.**  Edges `{(predIn u, u) : u ∈ U}` are then equal across
      `P₁, P₂`; the host block of `x` is the connected component of `x` in the predecessor graph
      (`hostSet P x = {minVal} ∪ {survivors with the same predIn-descent root}`), so equal edges
      ⇒ equal components ⇒ equal host blocks.

PROVED and available: `edge_tight_geom` (TIGHTNESS), `column_sep_geom` (COLUMN-SEP),
`span_laminar` (Lemma 2), `bridge_edge` (BRIDGE edge core), plus all of Forward's edge model
(`predIn_*`, `no_alt`, `lemmaA/B`, `survivorFamily`).

This theorem is now SORRY-FREE: stage (2) (component recovery) is fully proved here from
`predIn_forced` (stage 1, the single remaining `sorry`).  A block is recovered as the
`edgeStep`-component of its survivors together with its unique non-survivor `minVal` root; both
are forced because `T P` and the `predIn` map agree across `P₁, P₂`. -/
theorem hostSet_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {x : ZMod (d * m)} (hx₁ : x ∈ T P₁) (hx₂ : x ∈ T P₂) :
    hostSet P₁ x hx₁ = hostSet P₂ x hx₂ := by
  -- symmetric subset argument
  suffices H : ∀ (Q₁ Q₂ : Finset (Finset (ZMod (d*m)))), Portrait d m Q₁ → Portrait d m Q₂ →
      T Q₁ = T Q₂ → ∀ (y : ZMod (d*m)) (hy₁ : y ∈ T Q₁) (hy₂ : y ∈ T Q₂),
        hostSet Q₁ y hy₁ ⊆ hostSet Q₂ y hy₂ by
    exact Finset.Subset.antisymm (H P₁ P₂ h₁ h₂ hT x hx₁ hx₂)
      (H P₂ P₁ h₂ h₁ hT.symm x hx₂ hx₁)
  intro Q₁ Q₂ hQ₁ hQ₂ hTQ y hy₁ hy₂ z hz
  by_cases hzT : z ∈ T Q₁
  · -- z survivor of y's block: reachable from y in Q₁; transfer to Q₂.
    have hzhost : hostSet Q₁ z hzT = hostSet Q₁ y hy₁ :=
      hostSet_eq_of_mem hQ₁ hzT (hostSet_mem hy₁) hz
    have hreach₁ : Relation.ReflTransGen (edgeStep Q₁) z y := reach_of_sameHost hQ₁ hy₁ hzT hzhost
    have hzT₂ : z ∈ T Q₂ := hTQ ▸ hzT
    have hzhost₂ : hostSet Q₂ z hzT₂ = hostSet Q₂ y hy₂ :=
      reach_sameHost hQ₂ hy₂ (reach_symm (reach_forced hd hm hQ₁ hQ₂ hTQ hreach₁)) hzT₂
    rw [← hzhost₂]; exact mem_hostSet hzT₂
  · -- z ∉ T Q₁: z is the root (minVal) of y's Q₁-block.
    have hyne₁ : (hostSet Q₁ y hy₁).Nonempty := ⟨y, mem_hostSet hy₁⟩
    have hzmin : z = minVal (hostSet Q₁ y hy₁) hyne₁ := by
      by_contra hne
      exact hzT (mem_T.mpr ⟨_, hostSet_mem hy₁, (mem_eraseMin _ hyne₁ z).mpr ⟨hz, hne⟩⟩)
    obtain ⟨q, hq, hqpred, hqhost, hqreach⟩ := reach_to_low hQ₁ y.val y rfl hy₁
    have hqne : (hostSet Q₁ q hq).Nonempty := ⟨q, mem_hostSet hq⟩
    have hpq_min : predIn Q₁ q hq = minVal (hostSet Q₁ q hq) hqne := by
      by_contra hne
      exact hqpred (mem_T.mpr ⟨_, hostSet_mem hq,
        (mem_eraseMin _ hqne _).mpr ⟨predIn_mem_host hq, hne⟩⟩)
    have hpq_z : predIn Q₁ q hq = z := by
      rw [hpq_min, hzmin]; exact minVal_congr hqne hyne₁ hqhost
    have hq₂ : q ∈ T Q₂ := hTQ ▸ hq
    have hpredeq : predIn Q₁ q hq = predIn Q₂ q hq₂ := predIn_forced hd hm hQ₁ hQ₂ hTQ hq hq₂
    have hpq_z₂ : predIn Q₂ q hq₂ = z := by rw [← hpredeq]; exact hpq_z
    have hqhost₂ : hostSet Q₂ q hq₂ = hostSet Q₂ y hy₂ := by
      have hreach₁ : Relation.ReflTransGen (edgeStep Q₁) q y := reach_of_sameHost hQ₁ hy₁ hq hqhost
      exact reach_sameHost hQ₂ hy₂ (reach_symm (reach_forced hd hm hQ₁ hQ₂ hTQ hreach₁)) hq₂
    rw [← hqhost₂, ← hpq_z₂]; exact predIn_mem_host hq₂

/-! ### B-assembly: `T` injective. -/

/-- **INJECTIVITY (implication form).** Two portraits with equal survivor sets are equal. -/
theorem T_inj (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) : P₁ = P₂ := by
  haveI : NeZero (d*m) := ⟨by positivity⟩
  rw [portrait_eq_image_hostSet h₁, portrait_eq_image_hostSet h₂]
  -- The attach sets differ (T P₁ vs T P₂), so rewrite along hT and match the functions.
  apply Finset.ext
  intro S
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx₁⟩, _, hSeq⟩
    have hx₂ : x ∈ T P₂ := hT ▸ hx₁
    refine ⟨⟨x, hx₂⟩, Finset.mem_attach _ _, ?_⟩
    rw [← hSeq]
    exact (hostSet_forced hd hm h₁ h₂ hT hx₁ hx₂).symm
  · rintro ⟨⟨x, hx₂⟩, _, hSeq⟩
    have hx₁ : x ∈ T P₁ := hT.symm ▸ hx₂
    refine ⟨⟨x, hx₁⟩, Finset.mem_attach _ _, ?_⟩
    rw [← hSeq]
    exact hostSet_forced hd hm h₁ h₂ hT hx₁ hx₂

/-- **INJECTIVITY (`Set.InjOn` form, the stated target).** -/
theorem T_injOn (hd : 0 < d) (hm : 0 < m) :
    Set.InjOn (T (N := d*m)) {P | Portrait d m P} :=
  fun _P₁ h₁ _P₂ h₂ hT => T_inj hd hm h₁ h₂ hT

end CriticalPortraits

-- Axiom audit of the fully-proved (sorry-free) results (the structural substrate).
-- Stage-2 (component recovery) is sorry-free GIVEN the single keystone `predIn_forced`:
-- The KEYSTONE is now closed; the final results are sorry-free:
