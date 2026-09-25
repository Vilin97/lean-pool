/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordLabels

/-!
# The per-step crossing-parity decomposition

The chord-crossing count of a boundary pairing changes, across the
transposition of `pathMatch_repair_swap`, exactly by the
mutual-crossing change of the two re-paired chords: all third-chord
contributions cancel mod 2.  The count is a sum of ordered-pair
crossing indicators; splitting the index square by membership in the
four touched ends leaves an untouched block (termwise equal), a
mixed block (per-third-chord parity transfer, `third_chord_reparity`)
and the four-end block (evaluated to the mutual-crossing indicator).
-/

@[expose] public section

namespace RS



variable {α : Type}

/-- Symmetrized crossing of two chords given by (unordered) label
pairs: each chord is normalized low-to-high and the two normalized
chords interleave, in either order. -/
def chordPairCrossSym [LinearOrder α]
    (p q : α × α) : Prop :=
  ChordPairCross (min p.1 p.2) (max p.1 p.2) (min q.1 q.2)
      (max q.1 q.2) ∨
    ChordPairCross (min q.1 q.2) (max q.1 q.2) (min p.1 p.2)
      (max p.1 p.2)

/-- The symmetrization is redundant: `ChordPairCross` of normalized
chords is itself symmetric (its two disjuncts swap). -/
theorem chordPairCrossSym_iff [LinearOrder α]
    (p₁ p₂ q₁ q₂ : α) :
    chordPairCrossSym (p₁, p₂) (q₁, q₂) ↔
      ChordPairCross (min p₁ p₂) (max p₁ p₂) (min q₁ q₂)
        (max q₁ q₂) :=
  ⟨fun h => h.elim id (fun h => h.elim Or.inr Or.inl), Or.inl⟩

open scoped Classical in
/-- The two ordered crossing indicators of one sorted chord `(u, w)`
against a chord recorded as `(x, y)` sum to the interleaving
indicator, gated by `x < y`. -/
private theorem sorted_pair_sum [LinearOrder α]
    {x y u w : α} (huw : u < w) :
    ((if u < w ∧ x < y ∧ u < x ∧ x < w ∧ w < y then (1 : ℕ)
        else 0) +
      (if x < y ∧ u < w ∧ x < u ∧ u < y ∧ y < w then (1 : ℕ)
        else 0)) =
      if x < y ∧ ChordPairCross x y u w then (1 : ℕ) else 0 := by
  by_cases h1 : u < w ∧ x < y ∧ u < x ∧ x < w ∧ w < y
  · obtain ⟨-, hxy, hux, hxw, hwy⟩ := h1
    have h2 : ¬ (x < y ∧ u < w ∧ x < u ∧ u < y ∧ y < w) :=
      fun ⟨_, _, hxu, _, _⟩ => lt_asymm hux hxu
    rw [ite_eq_left ⟨huw, hxy, hux, hxw, hwy⟩, ite_eq_right h2,
      ite_eq_left ⟨hxy, Or.inr ⟨hux, hxw, hwy⟩⟩]
  · by_cases h2 : x < y ∧ u < w ∧ x < u ∧ u < y ∧ y < w
    · obtain ⟨hxy, -, hxu, huy, hyw⟩ := h2
      rw [ite_eq_right h1, ite_eq_left ⟨hxy, huw, hxu, huy, hyw⟩,
        ite_eq_left ⟨hxy, Or.inl ⟨hxu, huy, hyw⟩⟩]
    · have h3 : ¬ (x < y ∧ ChordPairCross x y u w) := by
        rintro ⟨hxy, ⟨hxu, huy, hyw⟩ | ⟨hux, hxw, hwy⟩⟩
        · exact h2 ⟨hxy, huw, hxu, huy, hyw⟩
        · exact h1 ⟨huw, hxy, hux, hxw, hwy⟩
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

open scoped Classical in
/-- The four ordered crossing indicators between one chord with ends
labelled `a`, `b` and a chord recorded as `(x, y)` sum to the gated
interleaving indicator of the normalized chords. -/
private theorem side_label_sum [LinearOrder α]
    {a b x y : α} (hab : a ≠ b) :
    (((if a < b ∧ x < y ∧ a < x ∧ x < b ∧ b < y then (1 : ℕ)
          else 0) +
        (if x < y ∧ a < b ∧ x < a ∧ a < y ∧ y < b then (1 : ℕ)
          else 0)) +
      ((if b < a ∧ x < y ∧ b < x ∧ x < a ∧ a < y then (1 : ℕ)
          else 0) +
        (if x < y ∧ b < a ∧ x < b ∧ b < y ∧ y < a then (1 : ℕ)
          else 0))) =
      if x < y ∧ ChordPairCross x y (min a b) (max a b)
        then (1 : ℕ) else 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · have e3 : (if b < a ∧ x < y ∧ b < x ∧ x < a ∧ a < y
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => lt_asymm h hc.1)
    have e4 : (if x < y ∧ b < a ∧ x < b ∧ b < y ∧ y < a
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => lt_asymm h hc.2.1)
    rw [e3, e4, add_zero, add_zero, min_eq_left h.le,
      max_eq_right h.le]
    exact sorted_pair_sum h
  · have e1 : (if a < b ∧ x < y ∧ a < x ∧ x < b ∧ b < y
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => lt_asymm h hc.1)
    have e2 : (if x < y ∧ a < b ∧ x < a ∧ a < y ∧ y < b
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => lt_asymm h hc.2.1)
    rw [e1, e2, zero_add, zero_add, min_eq_right h.le,
      max_eq_left h.le]
    exact sorted_pair_sum h

open scoped Classical in
/-- **The 16-pair table, cross-chord part**: the eight ordered
crossing indicators between two disjoint chords with end labels
`{a, b}` and `{c, d}` sum to the symmetrized mutual-crossing
indicator. -/
private theorem eight_label_sum [LinearOrder α]
    {a b c d : α} (hab : a ≠ b)
    (hcd : c ≠ d) :
    (((if a < b ∧ c < d ∧ a < c ∧ c < b ∧ b < d then (1 : ℕ)
          else 0) +
        (if a < b ∧ d < c ∧ a < d ∧ d < b ∧ b < c then (1 : ℕ)
          else 0)) +
      (((if b < a ∧ c < d ∧ b < c ∧ c < a ∧ a < d then (1 : ℕ)
            else 0) +
          (if b < a ∧ d < c ∧ b < d ∧ d < a ∧ a < c then (1 : ℕ)
            else 0)) +
        (((if c < d ∧ a < b ∧ c < a ∧ a < d ∧ d < b then (1 : ℕ)
              else 0) +
            (if c < d ∧ b < a ∧ c < b ∧ b < d ∧ d < a then (1 : ℕ)
              else 0)) +
          ((if d < c ∧ a < b ∧ d < a ∧ a < c ∧ c < b then (1 : ℕ)
              else 0) +
            (if d < c ∧ b < a ∧ d < b ∧ b < c ∧ c < a then (1 : ℕ)
              else 0))))) =
      if chordPairCrossSym (a, b) (c, d) then (1 : ℕ) else 0 := by
  have h₁ := side_label_sum (x := c) (y := d) hab
  have h₂ := side_label_sum (x := d) (y := c) hab
  have hsum :
      (if c < d ∧ ChordPairCross c d (min a b) (max a b)
        then (1 : ℕ) else 0) +
      (if d < c ∧ ChordPairCross d c (min a b) (max a b)
        then (1 : ℕ) else 0) =
      if chordPairCrossSym (a, b) (c, d) then (1 : ℕ) else 0 := by
    rw [chordPairCrossSym_iff]
    rcases lt_or_gt_of_ne hcd with h | h
    · simp [h, lt_asymm h, min_eq_left h.le, max_eq_right h.le,
        ChordPairCross, or_comm]
    · simp [h, lt_asymm h, min_eq_right h.le, max_eq_left h.le,
        ChordPairCross, or_comm]
  convert (congrArg₂ (· + ·) h₁ h₂).trans hsum using 1
  ac_rfl

/-- Sorting a chord in a cons-pair leaves the multiset unchanged. -/
private theorem minmax_cons [LinearOrder α]
    (u v : α) (s : Multiset α) :
    (min u v ::ₘ max u v ::ₘ s) = u ::ₘ v ::ₘ s := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact Multiset.cons_swap v u s

/-- The endpoint multisets of the two normalized re-pairings of four
labels agree. -/
private theorem minmax_multiset [LinearOrder α]
    (a b c d : α) :
    ({min a b, max a b, min c d, max c d} : Multiset α) =
      {min a c, max a c, min b d, max b d} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero]
  rw [minmax_cons, minmax_cons, minmax_cons, minmax_cons]
  exact congrArg (a ::ₘ ·) (Multiset.cons_swap b c _)

/-- Avoidance transfer to the normalized endpoint multiset. -/
private theorem minmax_multiset_forall [LinearOrder α]
    {a b c d x y : α}
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hcx : c ≠ x) (hcy : c ≠ y) (hdx : d ≠ x) (hdy : d ≠ y) :
    ∀ p ∈ ({min a b, max a b, min c d, max c d} : Multiset α),
      p ≠ x ∧ p ≠ y := by
  have h : ({min a b, max a b, min c d, max c d} : Multiset α) =
      {a, b, c, d} := by
    simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero]
    rw [minmax_cons, minmax_cons]
  rw [h]
  intro p hp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨hax, hay⟩
  · exact ⟨hbx, hby⟩
  · exact ⟨hcx, hcy⟩
  · exact ⟨hdx, hdy⟩

/-- Regrouping of two expanded quads into per-chord blocks. -/
private theorem add_block (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℕ) :
    (a₁ + (a₂ + (a₃ + a₄))) + (b₁ + (b₂ + (b₃ + b₄))) =
      ((a₁ + b₁) + (a₂ + b₂)) + ((a₃ + b₃) + (a₄ + b₄)) := by
  omega

/-- Splitting a square-indexed sum by a predicate on each factor. -/
private theorem sum_split_four {β : Type} (S : Finset β)
    (pr : β → Prop) [DecidablePred pr] (g : β → β → ℕ) :
    (∑ z ∈ S, ∑ z' ∈ S, g z z') =
      ((∑ z ∈ S.filter pr, ∑ z' ∈ S.filter pr, g z z') +
          ∑ z ∈ S.filter pr,
            ∑ z' ∈ S.filter (fun t => ¬ pr t), g z z') +
        ((∑ z ∈ S.filter (fun t => ¬ pr t),
            ∑ z' ∈ S.filter pr, g z z') +
          ∑ z ∈ S.filter (fun t => ¬ pr t),
            ∑ z' ∈ S.filter (fun t => ¬ pr t), g z z') := by
  have h1 : ∀ T : Finset β,
      (∑ z ∈ T, ∑ z' ∈ S, g z z') =
        (∑ z ∈ T, ∑ z' ∈ S.filter pr, g z z') +
          ∑ z ∈ T, ∑ z' ∈ S.filter (fun t => ¬ pr t), g z z' := by
    intro T
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun z _ =>
      (Finset.sum_filter_add_sum_filter_not S pr _).symm)
  rw [← Finset.sum_filter_add_sum_filter_not S pr
    (fun z => ∑ z' ∈ S, g z z'), h1, h1]

namespace EdgeSubset

open scoped Classical in
/-- The crossing indicator of two boundary ends, in terms of the
four labels, with designated matching partners. -/
private theorem chordCross_ite_eq
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {x y mx my : W.Flag}
    (hx : x ∈ F.boundaryFlags) (hy : y ∈ F.boundaryFlags)
    (hmx : mx ∈ F.boundaryFlags) (hmy : my ∈ F.boundaryFlags)
    (hpx : κ.pathMatch x hx = mx) (hpy : κ.pathMatch y hy = my) :
    (if ChordCross κ ⟨x, hx⟩ ⟨y, hy⟩ then (1 : ℕ) else 0) =
      if (F.boundaryLabel hx < F.boundaryLabel hmx ∧
          F.boundaryLabel hy < F.boundaryLabel hmy ∧
          F.boundaryLabel hx < F.boundaryLabel hy ∧
          F.boundaryLabel hy < F.boundaryLabel hmx ∧
          F.boundaryLabel hmx < F.boundaryLabel hmy)
        then (1 : ℕ) else 0 := by
  have h1 : F.boundaryLabel (κ.pathMatch_mem (Subtype.prop
      (⟨x, hx⟩ : {z : W.Flag // z ∈ F.boundaryFlags}))) =
      F.boundaryLabel hmx := boundaryLabel_congr _ hmx hpx
  have h2 : F.boundaryLabel (κ.pathMatch_mem (Subtype.prop
      (⟨y, hy⟩ : {z : W.Flag // z ∈ F.boundaryFlags}))) =
      F.boundaryLabel hmy := boundaryLabel_congr _ hmy hpy
  exact if_congr ((chordCross_iff_labels _ _).trans
    (by rw [h1, h2])) rfl rfl

open scoped Classical in
/-- A boundary end never crosses itself. -/
private theorem chordCross_self_ite
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {x : W.Flag} (hx : x ∈ F.boundaryFlags) :
    (if ChordCross κ ⟨x, hx⟩ ⟨x, hx⟩ then (1 : ℕ) else 0) = 0 :=
  ite_eq_right fun h => by
    obtain ⟨-, -, hlt, -, -⟩ := (chordCross_iff_labels _ _).mp h
    exact lt_irrefl _ hlt

open scoped Classical in
/-- The two ends of one chord never cross each other. -/
private theorem chordCross_partner_ite
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {x y : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hy : y ∈ F.boundaryFlags)
    (hyx : κ.pathMatch y hy = x) :
    (if ChordCross κ ⟨x, hx⟩ ⟨y, hy⟩ then (1 : ℕ) else 0) = 0 := by
  refine ite_eq_right (fun h => ?_)
  obtain ⟨-, hpartner, hstart, -, -⟩ := (chordCross_iff_labels _ _).mp h
  have h2 : F.boundaryLabel (κ.pathMatch_mem (Subtype.prop
      (⟨y, hy⟩ : {z : W.Flag // z ∈ F.boundaryFlags}))) =
      F.boundaryLabel hx := boundaryLabel_congr _ hx hyx
  exact lt_asymm hstart (h2 ▸ hpartner)

open scoped Classical in
/-- **The four-end block**: the full ordered-pair crossing sum over
the four ends of two disjoint chords is the symmetrized
mutual-crossing indicator of their label chords. -/
private theorem chordCross_quad_sum
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {u w p q : W.Flag}
    (hu : u ∈ F.boundaryFlags) (hw : w ∈ F.boundaryFlags)
    (hp : p ∈ F.boundaryFlags) (hq : q ∈ F.boundaryFlags)
    (huw : κ.pathMatch u hu = w) (hwu : κ.pathMatch w hw = u)
    (hpq : κ.pathMatch p hp = q) (hqp : κ.pathMatch q hq = p)
    (huw' : u ≠ w) (hup : u ≠ p) (huq : u ≠ q)
    (hwp : w ≠ p) (hwq : w ≠ q) (hpq' : p ≠ q) :
    (∑ z ∈ ({⟨u, hu⟩, ⟨w, hw⟩, ⟨p, hp⟩, ⟨q, hq⟩} :
        Finset {f : W.Flag // f ∈ F.boundaryFlags}),
      ∑ z' ∈ ({⟨u, hu⟩, ⟨w, hw⟩, ⟨p, hp⟩, ⟨q, hq⟩} :
        Finset {f : W.Flag // f ∈ F.boundaryFlags}),
        (if ChordCross κ z z' then (1 : ℕ) else 0)) =
      if chordPairCrossSym
          (F.boundaryLabel hu, F.boundaryLabel hw)
          (F.boundaryLabel hp, F.boundaryLabel hq)
        then (1 : ℕ) else 0 := by
  have nuw : (⟨u, hu⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨w, hw⟩ := fun h => huw' (congrArg Subtype.val h)
  have nup : (⟨u, hu⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨p, hp⟩ := fun h => hup (congrArg Subtype.val h)
  have nuq : (⟨u, hu⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨q, hq⟩ := fun h => huq (congrArg Subtype.val h)
  have nwp : (⟨w, hw⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨p, hp⟩ := fun h => hwp (congrArg Subtype.val h)
  have nwq : (⟨w, hw⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨q, hq⟩ := fun h => hwq (congrArg Subtype.val h)
  have npq : (⟨p, hp⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨q, hq⟩ := fun h => hpq' (congrArg Subtype.val h)
  simp only [sum_quad nuw nup nuq nwp nwq npq]
  rw [chordCross_self_ite κ hu, chordCross_self_ite κ hw,
    chordCross_self_ite κ hp, chordCross_self_ite κ hq,
    chordCross_partner_ite κ hu hw hwu,
    chordCross_partner_ite κ hw hu huw,
    chordCross_partner_ite κ hp hq hqp,
    chordCross_partner_ite κ hq hp hpq,
    chordCross_ite_eq κ hu hp hw hq huw hpq,
    chordCross_ite_eq κ hu hq hw hp huw hqp,
    chordCross_ite_eq κ hw hp hu hq hwu hpq,
    chordCross_ite_eq κ hw hq hu hp hwu hqp,
    chordCross_ite_eq κ hp hu hq hw hpq huw,
    chordCross_ite_eq κ hp hw hq hu hpq hwu,
    chordCross_ite_eq κ hq hu hp hw hqp huw,
    chordCross_ite_eq κ hq hw hp hu hqp hwu]
  simp only [add_zero, zero_add]
  exact eight_label_sum
    (fun h => huw' (boundaryLabel_inj hu hw h))
    (fun h => hpq' (boundaryLabel_inj hp hq h))

open scoped Classical in
/-- **One chord against a third end**: the four ordered crossing
indicators between the two ends of one chord and a fixed third end
sum to the gated interleaving indicator. -/
private theorem chordCross_side_sum
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {u w tv tm : W.Flag}
    (hu : u ∈ F.boundaryFlags) (hw : w ∈ F.boundaryFlags)
    (ht : tv ∈ F.boundaryFlags) (htmm : tm ∈ F.boundaryFlags)
    (huw : κ.pathMatch u hu = w) (hwu : κ.pathMatch w hw = u)
    (htm : κ.pathMatch tv ht = tm) (huw' : u ≠ w) :
    (((if ChordCross κ ⟨u, hu⟩ ⟨tv, ht⟩ then (1 : ℕ) else 0) +
        (if ChordCross κ ⟨tv, ht⟩ ⟨u, hu⟩ then (1 : ℕ) else 0)) +
      ((if ChordCross κ ⟨w, hw⟩ ⟨tv, ht⟩ then (1 : ℕ) else 0) +
        (if ChordCross κ ⟨tv, ht⟩ ⟨w, hw⟩ then (1 : ℕ) else 0))) =
      if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
          ChordPairCross (F.boundaryLabel ht)
            (F.boundaryLabel htmm)
            (min (F.boundaryLabel hu) (F.boundaryLabel hw))
            (max (F.boundaryLabel hu) (F.boundaryLabel hw)))
        then (1 : ℕ) else 0 := by
  rw [chordCross_ite_eq κ hu ht hw htmm huw htm,
    chordCross_ite_eq κ ht hu htmm hw htm huw,
    chordCross_ite_eq κ hw ht hu htmm hwu htm,
    chordCross_ite_eq κ ht hw htmm hu htm hwu]
  exact side_label_sum (fun h => huw' (boundaryLabel_inj hu hw h))

open scoped Classical in
/-- **The mixed block, per third chord**: for a fixed untouched end,
the eight ordered crossing indicators against the four touched ends
have the same parity before and after the transposition
(`third_chord_reparity` on the label chords). -/
private theorem touched_line_parity
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ κ' : F.RelTransitionSystem) {g₁ g₂ g₃ g₄ tv tm : W.Flag}
    (h₁ : g₁ ∈ F.boundaryFlags) (h₂ : g₂ ∈ F.boundaryFlags)
    (h₃ : g₃ ∈ F.boundaryFlags) (h₄ : g₄ ∈ F.boundaryFlags)
    (ht : tv ∈ F.boundaryFlags) (htmm : tm ∈ F.boundaryFlags)
    (k12 : κ.pathMatch g₁ h₁ = g₂) (k21 : κ.pathMatch g₂ h₂ = g₁)
    (k34 : κ.pathMatch g₃ h₃ = g₄) (k43 : κ.pathMatch g₄ h₄ = g₃)
    (k13 : κ'.pathMatch g₁ h₁ = g₃) (k31 : κ'.pathMatch g₃ h₃ = g₁)
    (k24 : κ'.pathMatch g₂ h₂ = g₄) (k42 : κ'.pathMatch g₄ h₄ = g₂)
    (htm : κ.pathMatch tv ht = tm) (htm' : κ'.pathMatch tv ht = tm)
    (h12 : g₁ ≠ g₂) (h13 : g₁ ≠ g₃) (h14 : g₁ ≠ g₄)
    (h23 : g₂ ≠ g₃) (h24 : g₂ ≠ g₄) (h34 : g₃ ≠ g₄)
    (n1t : g₁ ≠ tv) (n2t : g₂ ≠ tv) (n3t : g₃ ≠ tv)
    (n4t : g₄ ≠ tv)
    (n1m : g₁ ≠ tm) (n2m : g₂ ≠ tm) (n3m : g₃ ≠ tm)
    (n4m : g₄ ≠ tm) :
    ((∑ z ∈ ({⟨g₁, h₁⟩, ⟨g₂, h₂⟩, ⟨g₃, h₃⟩, ⟨g₄, h₄⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}),
        (if ChordCross κ z ⟨tv, ht⟩ then (1 : ℕ) else 0)) +
      ∑ z ∈ ({⟨g₁, h₁⟩, ⟨g₂, h₂⟩, ⟨g₃, h₃⟩, ⟨g₄, h₄⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}),
        (if ChordCross κ ⟨tv, ht⟩ z then (1 : ℕ) else 0)) % 2 =
    ((∑ z ∈ ({⟨g₁, h₁⟩, ⟨g₂, h₂⟩, ⟨g₃, h₃⟩, ⟨g₄, h₄⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}),
        (if ChordCross κ' z ⟨tv, ht⟩ then (1 : ℕ) else 0)) +
      ∑ z ∈ ({⟨g₁, h₁⟩, ⟨g₂, h₂⟩, ⟨g₃, h₃⟩, ⟨g₄, h₄⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}),
        (if ChordCross κ' ⟨tv, ht⟩ z then (1 : ℕ) else 0)) % 2 := by
  have nz12 : (⟨g₁, h₁⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨g₂, h₂⟩ := fun h => h12 (congrArg Subtype.val h)
  have nz13 : (⟨g₁, h₁⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨g₃, h₃⟩ := fun h => h13 (congrArg Subtype.val h)
  have nz14 : (⟨g₁, h₁⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨g₄, h₄⟩ := fun h => h14 (congrArg Subtype.val h)
  have nz23 : (⟨g₂, h₂⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨g₃, h₃⟩ := fun h => h23 (congrArg Subtype.val h)
  have nz24 : (⟨g₂, h₂⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨g₄, h₄⟩ := fun h => h24 (congrArg Subtype.val h)
  have nz34 : (⟨g₃, h₃⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨g₄, h₄⟩ := fun h => h34 (congrArg Subtype.val h)
  have nz32 : (⟨g₃, h₃⟩ : {f : W.Flag // f ∈ F.boundaryFlags}) ≠
      ⟨g₂, h₂⟩ := fun h => h23 (congrArg Subtype.val h).symm
  -- reorder the four ends on the repaired side to pair the chords
  -- ═══════ THE FOUR ENDS AS AN EXPLICIT QUADRUPLE ═══════
  -- Above: the four are pairwise distinct.  Below: the sum over the
  -- touched block expands into its sixteen ordered pairs.
  have hQ : ({⟨g₁, h₁⟩, ⟨g₂, h₂⟩, ⟨g₃, h₃⟩, ⟨g₄, h₄⟩} :
        Finset {f : W.Flag // f ∈ F.boundaryFlags}) =
      ({⟨g₁, h₁⟩, ⟨g₃, h₃⟩, ⟨g₂, h₂⟩, ⟨g₄, h₄⟩} :
        Finset {f : W.Flag // f ∈ F.boundaryFlags}) :=
    congrArg (insert (⟨g₁, h₁⟩ : {f : W.Flag // f ∈ F.boundaryFlags}))
      (Finset.insert_comm
        (⟨g₂, h₂⟩ : {f : W.Flag // f ∈ F.boundaryFlags})
        ⟨g₃, h₃⟩ {⟨g₄, h₄⟩})
  conv_rhs => rw [hQ]
  simp only [sum_quad nz12 nz13 nz14 nz23 nz24 nz34,
    sum_quad nz13 nz12 nz14 nz32 nz34 nz24]
  rw [add_block, add_block,
    chordCross_side_sum κ h₁ h₂ ht htmm k12 k21 htm h12,
    chordCross_side_sum κ h₃ h₄ ht htmm k34 k43 htm h34,
    chordCross_side_sum κ' h₁ h₃ ht htmm k13 k31 htm' h13,
    chordCross_side_sum κ' h₂ h₄ ht htmm k24 k42 htm' h24]
  by_cases hxy : F.boundaryLabel ht < F.boundaryLabel htmm
  · have r₁ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₁) (F.boundaryLabel h₂))
          (max (F.boundaryLabel h₁) (F.boundaryLabel h₂)))
        then (1 : ℕ) else 0) =
        if ChordPairCross (F.boundaryLabel ht)
            (F.boundaryLabel htmm)
            (min (F.boundaryLabel h₁) (F.boundaryLabel h₂))
            (max (F.boundaryLabel h₁) (F.boundaryLabel h₂))
          then (1 : ℕ) else 0 :=
      if_congr (and_iff_right hxy) rfl rfl
    have r₂ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₃) (F.boundaryLabel h₄))
          (max (F.boundaryLabel h₃) (F.boundaryLabel h₄)))
        then (1 : ℕ) else 0) =
        if ChordPairCross (F.boundaryLabel ht)
            (F.boundaryLabel htmm)
            (min (F.boundaryLabel h₃) (F.boundaryLabel h₄))
            (max (F.boundaryLabel h₃) (F.boundaryLabel h₄))
          then (1 : ℕ) else 0 :=
      if_congr (and_iff_right hxy) rfl rfl
    have r₃ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₁) (F.boundaryLabel h₃))
          (max (F.boundaryLabel h₁) (F.boundaryLabel h₃)))
        then (1 : ℕ) else 0) =
        if ChordPairCross (F.boundaryLabel ht)
            (F.boundaryLabel htmm)
            (min (F.boundaryLabel h₁) (F.boundaryLabel h₃))
            (max (F.boundaryLabel h₁) (F.boundaryLabel h₃))
          then (1 : ℕ) else 0 :=
      if_congr (and_iff_right hxy) rfl rfl
    have r₄ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₂) (F.boundaryLabel h₄))
          (max (F.boundaryLabel h₂) (F.boundaryLabel h₄)))
        then (1 : ℕ) else 0) =
        if ChordPairCross (F.boundaryLabel ht)
            (F.boundaryLabel htmm)
            (min (F.boundaryLabel h₂) (F.boundaryLabel h₄))
            (max (F.boundaryLabel h₂) (F.boundaryLabel h₄))
          then (1 : ℕ) else 0 :=
      if_congr (and_iff_right hxy) rfl rfl
    rw [r₁, r₂, r₃, r₄]
    exact third_chord_reparity
      (min_lt_max.mpr (fun h => h12 (boundaryLabel_inj h₁ h₂ h)))
      (min_lt_max.mpr (fun h => h34 (boundaryLabel_inj h₃ h₄ h)))
      (min_lt_max.mpr (fun h => h13 (boundaryLabel_inj h₁ h₃ h)))
      (min_lt_max.mpr (fun h => h24 (boundaryLabel_inj h₂ h₄ h)))
      (minmax_multiset _ _ _ _)
      (minmax_multiset_forall
        (fun h => n1t (boundaryLabel_inj h₁ ht h))
        (fun h => n1m (boundaryLabel_inj h₁ htmm h))
        (fun h => n2t (boundaryLabel_inj h₂ ht h))
        (fun h => n2m (boundaryLabel_inj h₂ htmm h))
        (fun h => n3t (boundaryLabel_inj h₃ ht h))
        (fun h => n3m (boundaryLabel_inj h₃ htmm h))
        (fun h => n4t (boundaryLabel_inj h₄ ht h))
        (fun h => n4m (boundaryLabel_inj h₄ htmm h)))
  · have z₁ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₁) (F.boundaryLabel h₂))
          (max (F.boundaryLabel h₁) (F.boundaryLabel h₂)))
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => hxy hc.1)
    have z₂ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₃) (F.boundaryLabel h₄))
          (max (F.boundaryLabel h₃) (F.boundaryLabel h₄)))
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => hxy hc.1)
    have z₃ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₁) (F.boundaryLabel h₃))
          (max (F.boundaryLabel h₁) (F.boundaryLabel h₃)))
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => hxy hc.1)
    have z₄ : (if (F.boundaryLabel ht < F.boundaryLabel htmm ∧
        ChordPairCross (F.boundaryLabel ht) (F.boundaryLabel htmm)
          (min (F.boundaryLabel h₂) (F.boundaryLabel h₄))
          (max (F.boundaryLabel h₂) (F.boundaryLabel h₄)))
        then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun hc => hxy hc.1)
    rw [z₁, z₂, z₃, z₄]

/-- The touched part of the boundary is exactly the four ends of the
two re-paired chords. -/
private theorem filter_touched_eq {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags) :
    F.boundaryFlags.attach.filter
        (fun t => t.val = e₁ ∨ t.val = κ.pathMatch e₁ he₁ ∨
          t.val = e₂ ∨ t.val = κ.pathMatch e₂ he₂) =
      ({⟨e₁, he₁⟩, ⟨κ.pathMatch e₁ he₁, κ.pathMatch_mem he₁⟩,
        ⟨e₂, he₂⟩, ⟨κ.pathMatch e₂ he₂, κ.pathMatch_mem he₂⟩} :
        Finset {f : W.Flag // f ∈ F.boundaryFlags}) := by
  ext b
  obtain ⟨v, hv⟩ := b
  simp only [Finset.mem_filter, Finset.mem_attach, true_and,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]

open scoped Classical in
/-- **The per-step crossing-parity decomposition**: across a pairing
transposition (two ends of distinct chords re-pair, the far ends
re-pair with each other, everything else is preserved), the crossing
count changes mod 2 exactly by the mutual-crossing change of the two
re-paired chords. -/
theorem chordCrossingCount_repair_parity
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem} {e₁ e₂ : W.Flag}
    (he₁ : e₁ ∈ F.boundaryFlags) (he₂ : e₂ ∈ F.boundaryFlags)
    (hne : e₁ ≠ e₂) (hPne : κ.pathMatch e₁ he₁ ≠ e₂)
    (hcross : κ'.pathMatch e₁ he₁ = e₂)
    (hfar : κ'.pathMatch (κ.pathMatch e₁ he₁)
      (κ.pathMatch_mem he₁) = κ.pathMatch e₂ he₂)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ e₁ → δ ≠ e₂ → δ ≠ κ.pathMatch e₁ he₁ →
      δ ≠ κ.pathMatch e₂ he₂ →
      κ'.pathMatch δ hδ = κ.pathMatch δ hδ) :
    (chordCrossingCount κ + chordCrossingCount κ') % 2 =
      ((if chordPairCrossSym
            (F.boundaryLabel he₁,
              F.boundaryLabel (κ.pathMatch_mem he₁))
            (F.boundaryLabel he₂,
              F.boundaryLabel (κ.pathMatch_mem he₂))
          then (1 : ℕ) else 0) +
        (if chordPairCrossSym
            (F.boundaryLabel he₁, F.boundaryLabel he₂)
            (F.boundaryLabel (κ.pathMatch_mem he₁),
              F.boundaryLabel (κ.pathMatch_mem he₂))
          then (1 : ℕ) else 0)) % 2 := by
  -- ═══════ SETUP: THE FOUR TOUCHED ENDS ═══════
  -- involutions of the two pairings on the four ends
  have hinv₁ : κ.pathMatch (κ.pathMatch e₁ he₁)
      (κ.pathMatch_mem he₁) = e₁ := κ.pathMatch_invol he₁
  have hinv₂ : κ.pathMatch (κ.pathMatch e₂ he₂)
      (κ.pathMatch_mem he₂) = e₂ := κ.pathMatch_invol he₂
  have hcross' : κ'.pathMatch e₂ he₂ = e₁ :=
    (κ'.pathMatch_congr hcross.symm he₂
      (κ'.pathMatch_mem he₁)).trans (κ'.pathMatch_invol he₁)
  have hfar' : κ'.pathMatch (κ.pathMatch e₂ he₂)
      (κ.pathMatch_mem he₂) = κ.pathMatch e₁ he₁ :=
    (κ'.pathMatch_congr hfar.symm (κ.pathMatch_mem he₂)
      (κ'.pathMatch_mem (κ.pathMatch_mem he₁))).trans
      (κ'.pathMatch_invol (κ.pathMatch_mem he₁))
  -- the four touched ends are pairwise distinct
  have hd12 : e₁ ≠ κ.pathMatch e₁ he₁ :=
    fun h => κ.pathMatch_ne_self he₁ h.symm
  have hd14 : e₁ ≠ κ.pathMatch e₂ he₂ := fun h =>
    hPne ((κ.pathMatch_congr h he₁
      (κ.pathMatch_mem he₂)).trans hinv₂)
  have hd23 : κ.pathMatch e₁ he₁ ≠ e₂ := hPne
  have hd24 : κ.pathMatch e₁ he₁ ≠ κ.pathMatch e₂ he₂ := fun h =>
    hne (hinv₁.symm.trans ((κ.pathMatch_congr h
      (κ.pathMatch_mem he₁) (κ.pathMatch_mem he₂)).trans hinv₂))
  have hd34 : e₂ ≠ κ.pathMatch e₂ he₂ :=
    fun h => κ.pathMatch_ne_self he₂ h.symm
  -- ═══════ STAGE 1: THE COUNT AS AN ORDERED-PAIR SUM ═══════
  have hcard : ∀ κ₀ : F.RelTransitionSystem,
      chordCrossingCount κ₀ =
        ∑ z ∈ F.boundaryFlags.attach,
          ∑ z' ∈ F.boundaryFlags.attach,
            (if ChordCross κ₀ z z' then (1 : ℕ) else 0) := by
    intro κ₀
    unfold chordCrossingCount
    rw [Finset.card_filter, Finset.sum_product]
  -- ═══════ STAGE 2: THE FOUR-END BLOCK ═══════
  -- the repaired four-end block, with the ends listed chord-first
  have hA' : (∑ z ∈ ({⟨e₁, he₁⟩,
        ⟨κ.pathMatch e₁ he₁, κ.pathMatch_mem he₁⟩, ⟨e₂, he₂⟩,
        ⟨κ.pathMatch e₂ he₂, κ.pathMatch_mem he₂⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}),
      ∑ z' ∈ ({⟨e₁, he₁⟩,
        ⟨κ.pathMatch e₁ he₁, κ.pathMatch_mem he₁⟩, ⟨e₂, he₂⟩,
        ⟨κ.pathMatch e₂ he₂, κ.pathMatch_mem he₂⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}),
        (if ChordCross κ' z z' then (1 : ℕ) else 0)) =
      if chordPairCrossSym
          (F.boundaryLabel he₁, F.boundaryLabel he₂)
          (F.boundaryLabel (κ.pathMatch_mem he₁),
            F.boundaryLabel (κ.pathMatch_mem he₂))
        then (1 : ℕ) else 0 := by
    have hlit : ({⟨e₁, he₁⟩,
        ⟨κ.pathMatch e₁ he₁, κ.pathMatch_mem he₁⟩, ⟨e₂, he₂⟩,
        ⟨κ.pathMatch e₂ he₂, κ.pathMatch_mem he₂⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}) =
        ({⟨e₁, he₁⟩, ⟨e₂, he₂⟩,
          ⟨κ.pathMatch e₁ he₁, κ.pathMatch_mem he₁⟩,
          ⟨κ.pathMatch e₂ he₂, κ.pathMatch_mem he₂⟩} :
          Finset {f : W.Flag // f ∈ F.boundaryFlags}) :=
      congrArg
        (insert (⟨e₁, he₁⟩ : {f : W.Flag // f ∈ F.boundaryFlags}))
        (Finset.insert_comm
          (⟨κ.pathMatch e₁ he₁, κ.pathMatch_mem he₁⟩ :
            {f : W.Flag // f ∈ F.boundaryFlags})
          ⟨e₂, he₂⟩ {⟨κ.pathMatch e₂ he₂, κ.pathMatch_mem he₂⟩})
    rw [hlit]
    exact chordCross_quad_sum κ' he₁ he₂ (κ.pathMatch_mem he₁)
      (κ.pathMatch_mem he₂) hcross hcross' hfar hfar' hne hd12
      hd14 (fun h => hd23 h.symm) hd34 hd24
  -- ═══════ STAGE 3: THE UNTOUCHED BLOCK IS TERMWISE EQUAL ═══════
  have hD : (∑ z ∈ F.boundaryFlags.attach.filter
        (fun t => ¬ (t.val = e₁ ∨ t.val = κ.pathMatch e₁ he₁ ∨
          t.val = e₂ ∨ t.val = κ.pathMatch e₂ he₂)),
      ∑ z' ∈ F.boundaryFlags.attach.filter
        (fun t => ¬ (t.val = e₁ ∨ t.val = κ.pathMatch e₁ he₁ ∨
          t.val = e₂ ∨ t.val = κ.pathMatch e₂ he₂)),
        (if ChordCross κ' z z' then (1 : ℕ) else 0)) =
      ∑ z ∈ F.boundaryFlags.attach.filter
        (fun t => ¬ (t.val = e₁ ∨ t.val = κ.pathMatch e₁ he₁ ∨
          t.val = e₂ ∨ t.val = κ.pathMatch e₂ he₂)),
      ∑ z' ∈ F.boundaryFlags.attach.filter
        (fun t => ¬ (t.val = e₁ ∨ t.val = κ.pathMatch e₁ he₁ ∨
          t.val = e₂ ∨ t.val = κ.pathMatch e₂ he₂)),
        (if ChordCross κ z z' then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun z hz =>
      Finset.sum_congr rfl (fun z' hz' => ?_))
    have hnz := (Finset.mem_filter.mp hz).2
    have hnz' := (Finset.mem_filter.mp hz').2
    have hzeq : κ'.pathMatch z.val z.prop =
        κ.pathMatch z.val z.prop :=
      hout z.val z.prop (fun h => hnz (Or.inl h))
        (fun h => hnz (Or.inr (Or.inr (Or.inl h))))
        (fun h => hnz (Or.inr (Or.inl h)))
        (fun h => hnz (Or.inr (Or.inr (Or.inr h))))
    have hz'eq : κ'.pathMatch z'.val z'.prop =
        κ.pathMatch z'.val z'.prop :=
      hout z'.val z'.prop (fun h => hnz' (Or.inl h))
        (fun h => hnz' (Or.inr (Or.inr (Or.inl h))))
        (fun h => hnz' (Or.inr (Or.inl h)))
        (fun h => hnz' (Or.inr (Or.inr (Or.inr h))))
    exact if_congr (by unfold ChordCross; rw [hzeq, hz'eq])
      rfl rfl
  -- ═══════ ASSEMBLY: THE MOD-2 BOOKKEEPING ═══════
  have key : ∀ A₁ A₂ B₁ C₁ B₂ C₂ D : ℕ,
      (B₁ + C₁) % 2 = (B₂ + C₂) % 2 →
      (((A₁ + B₁) + (C₁ + D)) + ((A₂ + B₂) + (C₂ + D))) % 2 =
        (A₁ + A₂) % 2 := by
    intro A₁ A₂ B₁ C₁ B₂ C₂ D h
    omega
  rw [hcard κ, hcard κ',
    sum_split_four F.boundaryFlags.attach
      (fun t => t.val = e₁ ∨ t.val = κ.pathMatch e₁ he₁ ∨
        t.val = e₂ ∨ t.val = κ.pathMatch e₂ he₂),
    sum_split_four F.boundaryFlags.attach
      (fun t => t.val = e₁ ∨ t.val = κ.pathMatch e₁ he₁ ∨
        t.val = e₂ ∨ t.val = κ.pathMatch e₂ he₂),
    filter_touched_eq κ he₁ he₂,
    chordCross_quad_sum κ he₁ (κ.pathMatch_mem he₁) he₂
      (κ.pathMatch_mem he₂) rfl hinv₁ rfl hinv₂ hd12 hne hd14
      hd23 hd24 hd34,
    hA', hD]
  refine key _ _ _ _ _ _ _ ?_
  rw [Finset.sum_comm, ← Finset.sum_add_distrib,
    Finset.sum_comm, ← Finset.sum_add_distrib]
  refine (Finset.sum_nat_mod _ 2 _).trans
    (Eq.trans ?_ (Finset.sum_nat_mod _ 2 _).symm)
  refine congrArg (· % 2)
    (Finset.sum_congr rfl (fun t htN => ?_))
  have hnt := (Finset.mem_filter.mp htN).2
  have nt1 : t.val ≠ e₁ := fun h => hnt (Or.inl h)
  have nt2 : t.val ≠ κ.pathMatch e₁ he₁ :=
    fun h => hnt (Or.inr (Or.inl h))
  have nt3 : t.val ≠ e₂ :=
    fun h => hnt (Or.inr (Or.inr (Or.inl h)))
  have nt4 : t.val ≠ κ.pathMatch e₂ he₂ :=
    fun h => hnt (Or.inr (Or.inr (Or.inr h)))
  have htm' : κ'.pathMatch t.val t.prop =
      κ.pathMatch t.val t.prop :=
    hout t.val t.prop nt1 nt3 nt2 nt4
  have m1 : e₁ ≠ κ.pathMatch t.val t.prop := fun h =>
    nt2 (((κ.pathMatch_congr h he₁
      (κ.pathMatch_mem t.prop)).trans
      (κ.pathMatch_invol t.prop)).symm)
  have m2 : κ.pathMatch e₁ he₁ ≠ κ.pathMatch t.val t.prop :=
    fun h => nt1 ((hinv₁.symm.trans ((κ.pathMatch_congr h
      (κ.pathMatch_mem he₁) (κ.pathMatch_mem t.prop)).trans
      (κ.pathMatch_invol t.prop))).symm)
  have m3 : e₂ ≠ κ.pathMatch t.val t.prop := fun h =>
    nt4 (((κ.pathMatch_congr h he₂
      (κ.pathMatch_mem t.prop)).trans
      (κ.pathMatch_invol t.prop)).symm)
  have m4 : κ.pathMatch e₂ he₂ ≠ κ.pathMatch t.val t.prop :=
    fun h => nt3 ((hinv₂.symm.trans ((κ.pathMatch_congr h
      (κ.pathMatch_mem he₂) (κ.pathMatch_mem t.prop)).trans
      (κ.pathMatch_invol t.prop))).symm)
  exact touched_line_parity κ κ' he₁ (κ.pathMatch_mem he₁) he₂
    (κ.pathMatch_mem he₂) t.prop (κ.pathMatch_mem t.prop)
    rfl hinv₁ rfl hinv₂ hcross hcross' hfar hfar' rfl htm'
    hd12 hne hd14 hd23 hd24 hd34
    (fun h => nt1 h.symm) (fun h => nt2 h.symm)
    (fun h => nt3 h.symm) (fun h => nt4 h.symm) m1 m2 m3 m4

end EdgeSubset

end RS
