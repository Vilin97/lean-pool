/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.LabelChords

/-!
# The gluing action on chord diagrams

Gluing the cut `{i, j}` acts on label chord diagrams: the chord
`(i, j)` closes into a loop; otherwise the chords at `i` and at `j`
concatenate into one chord joining their far ends; chords avoiding
the cut pass through.  This is the combinatorial (Temperley–Lieb)
composition over which the pairing-resolved gluing decomposition
lives.
-/

namespace RS

open scoped Classical

variable {α : Type}

open Classical in
/-- The far end of the chord at `x`, when one exists. -/
noncomputable def cutPartner [LinearOrder α]
    (P : Finset (α × α)) (x : α) :
    Option α :=
  if h : ∃ y, (min x y, max x y) ∈ P then
    some (Classical.choose h)
  else none

open Classical in
/-- The glued diagram. -/
noncomputable def glueChords [LinearOrder α]
    (i j : α) (P : Finset (α × α)) :
    Finset (α × α) :=
  match cutPartner P i, cutPartner P j with
  | some x, some y =>
      if x = j then P.erase (min i j, max i j)
      else ((P.erase (min i x, max i x)).erase
          (min j y, max j y)) ∪ {(min x y, max x y)}
  | _, _ => P

/-- In a well-formed diagram a chord end determines its far end. -/
theorem cutPartner_eq_some [LinearOrder α]
    {P : Finset (α × α)}
    (hP : IsChordDiagram P) {x y : α}
    (h : (min x y, max x y) ∈ P) : cutPartner P x = some y := by
  have hex : ∃ z, (min x z, max x z) ∈ P := ⟨y, h⟩
  rw [cutPartner, dif_pos hex]
  have hch := Classical.choose_spec hex
  have hxy : x ≠ y := by
    intro he
    subst he
    have h1 := hP.ordered _ h
    simp only [min_self, max_self] at h1
    exact lt_irrefl x h1
  have hxz : x ≠ Classical.choose hex := by
    intro he
    have h1 := hP.ordered _ hch
    rw [← he] at h1
    simp only [min_self, max_self] at h1
    exact lt_irrefl x h1
  by_cases heq : (min x y, max x y) =
      (min x (Classical.choose hex), max x (Classical.choose hex))
  · -- equal sorted pairs with a common member force equal partners
    have h1 : min x y = min x (Classical.choose hex) :=
      congrArg Prod.fst heq
    have h2 : max x y = max x (Classical.choose hex) :=
      congrArg Prod.snd heq
    have hz : y = Classical.choose hex := by
      rcases le_total x y with hle | hle <;>
        rcases le_total x (Classical.choose hex) with hle' | hle'
      · exact (max_eq_right hle).symm.trans
          (h2.trans (max_eq_right hle'))
      · exact absurd ((min_eq_left hle).symm.trans
          (h1.trans (min_eq_right hle'))) hxz
      · exact absurd (((min_eq_right hle).symm.trans
          (h1.trans (min_eq_left hle'))).symm) hxy
      · exact (min_eq_right hle).symm.trans
          (h1.trans (min_eq_right hle'))
    exact congrArg some hz.symm
  · exfalso
    have hdisj := hP.disjoint _ h _ hch heq
    rcases le_total x y with hle | hle <;>
      rcases le_total x (Classical.choose hex) with hle' | hle'
    · exact hdisj.fst_ne_fst
        ((min_eq_left hle).trans (min_eq_left hle').symm)
    · exact hdisj.fst_ne_snd
        ((min_eq_left hle).trans (max_eq_left hle').symm)
    · exact hdisj.snd_ne_fst
        ((max_eq_left hle).trans (min_eq_left hle').symm)
    · exact hdisj.snd_ne_snd
        ((max_eq_left hle).trans (max_eq_left hle').symm)

/-- Well-formedness is inherited by subdiagrams. -/
theorem IsChordDiagram.mono [LinearOrder α]
    {P Q : Finset (α × α)}
    (hQP : Q ⊆ P) (hP : IsChordDiagram P) : IsChordDiagram Q :=
  ⟨fun p hp => hP.ordered p (hQP hp),
    fun p hp q hq hne => hP.disjoint p (hQP hp) q (hQP hq) hne⟩

/-- The glued diagram of a crossing cut: the chords at the two cut
labels concatenate. -/
theorem glueChords_cross [LinearOrder α]
    {P : Finset (α × α)}
    (hP : IsChordDiagram P) {i j x y : α} (hxj : x ≠ j)
    (hi : (min i x, max i x) ∈ P) (hj : (min j y, max j y) ∈ P) :
    glueChords i j P =
      ((P.erase (min i x, max i x)).erase (min j y, max j y)) ∪
        {(min x y, max x y)} := by
  rw [glueChords, cutPartner_eq_some hP hi,
    cutPartner_eq_some hP hj]
  simp only [if_neg hxj]

end RS
