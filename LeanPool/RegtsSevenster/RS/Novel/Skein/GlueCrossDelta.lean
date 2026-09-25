/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueChords

/-!
# The crossing-parity delta of the diagram gluing

The crossing-count parity change of a label chord diagram across
the Temperley–Lieb gluing `glueChords i j` — the chord-sign ratio
the converse's per-cut splitting carries.

* `diagCrossCount` — the abstract crossing count of a chord
  diagram: ordered pairs of chords, gated so that the first-starting
  chord is listed first; for a well-formed diagram each crossing
  unordered pair contributes exactly one element.
* `diagCrossCount_glue_cross` — **the glue delta**: gluing the cut
  `{i, j}` (chords `(i,x)`, `(j,y)` concatenating into `(x,y)`)
  changes the crossing parity by the number of surviving chords
  crossing the cut, plus the mutual-crossing indicator of the two
  cut chords.
-/

namespace RS



variable {α : Type}

/-- `ChordPairCross` is symmetric in its two chords: the two
disjuncts swap. -/
theorem chordPairCross_comm [LinearOrder α]
    {x y u w : α} :
    ChordPairCross x y u w ↔ ChordPairCross u w x y :=
  or_comm

open Classical in
/-- **The abstract diagram crossing count**: ordered pairs of
chords that interleave, gated so the first-starting chord is listed
first.  On a well-formed diagram (`IsChordDiagram`) every crossing
unordered pair of chords contributes exactly one ordered pair, so
this is the plain crossing number. -/
noncomputable def diagCrossCount [LinearOrder α]
    (P : Finset (α × α)) : ℕ :=
  ((P ×ˢ P).filter (fun pq => pq.1.1 < pq.2.1 ∧
    ChordPairCross pq.1.1 pq.1.2 pq.2.1 pq.2.2)).card

open Classical in
/-- The gated ordered crossing indicator of two chords. -/
private noncomputable def xInd [LinearOrder α]
    (p q : α × α) : ℕ :=
  if p.1 < q.1 ∧ ChordPairCross p.1 p.2 q.1 q.2 then 1 else 0

private theorem diagCrossCount_eq_sum [LinearOrder α]
    (P : Finset (α × α)) :
    diagCrossCount P = ∑ p ∈ P, ∑ q ∈ P, xInd p q := by
  unfold diagCrossCount xInd
  rw [Finset.card_filter, Finset.sum_product]

private theorem xInd_self [LinearOrder α]
    (p : α × α) : xInd p p = 0 :=
  ite_eq_right (fun h => lt_irrefl _ h.1)

/-- The two ordered indicators of a chord pair with distinct starts
sum to the plain crossing indicator. -/
private theorem xInd_pair [LinearOrder α]
    {p q : α × α} (h : p.1 ≠ q.1) :
    xInd p q + xInd q p =
      if ChordPairCross p.1 p.2 q.1 q.2 then 1 else 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have e0 : xInd q p = 0 := by
      unfold xInd
      exact ite_eq_right (fun hc => lt_asymm hlt hc.1)
    rw [e0, add_zero]
    unfold xInd
    exact if_congr (and_iff_right hlt) rfl rfl
  · have e0 : xInd p q = 0 := by
      unfold xInd
      exact ite_eq_right (fun hc => lt_asymm hgt hc.1)
    rw [e0, zero_add]
    unfold xInd
    exact if_congr ((and_iff_right hgt).trans chordPairCross_comm)
      rfl rfl

/-- Inserting a fresh chord adds its ordered indicators against the
old diagram. -/
private theorem diagCrossCount_insert [LinearOrder α]
    {P : Finset (α × α)}
    {c : α × α} (hc : c ∉ P) :
    diagCrossCount (insert c P) = diagCrossCount P +
      ∑ p ∈ P, (xInd c p + xInd p c) := by
  rw [diagCrossCount_eq_sum, diagCrossCount_eq_sum,
    Finset.sum_insert hc, Finset.sum_insert hc, xInd_self,
    zero_add]
  rw [show (∑ p ∈ P, ∑ q ∈ insert c P, xInd p q) =
      ∑ p ∈ P, (xInd p c + ∑ q ∈ P, xInd p q) from
    Finset.sum_congr rfl (fun p _ => Finset.sum_insert hc),
    Finset.sum_add_distrib]
  rw [show (∑ p ∈ P, (xInd c p + xInd p c)) =
      (∑ p ∈ P, xInd c p) + ∑ p ∈ P, xInd p c from
    Finset.sum_add_distrib]
  omega

/-! ## Order helpers -/

/-- A point distinct from both sorted ends is distinct from both
raw ends. -/
private theorem ne_ends_raw [LinearOrder α]
    {z a b : α} (h1 : z ≠ min a b)
    (h2 : z ≠ max a b) : z ≠ a ∧ z ≠ b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    exact ⟨h1, h2⟩
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    exact ⟨h2, h1⟩

/-- The ends of any other chord of a well-formed diagram avoid the
raw ends of a sorted chord. -/
private theorem ends_ne [LinearOrder α]
    {P : Finset (α × α)} (hP : IsChordDiagram P)
    {a b : α} {q : α × α} (hab : (min a b, max a b) ∈ P)
    (hq : q ∈ P) (hne : q ≠ (min a b, max a b)) :
    (q.1 ≠ a ∧ q.1 ≠ b) ∧ (q.2 ≠ a ∧ q.2 ≠ b) := by
  have hd := hP.disjoint q hq _ hab hne
  exact ⟨ne_ends_raw hd.fst_ne_fst hd.fst_ne_snd,
    ne_ends_raw hd.snd_ne_fst hd.snd_ne_snd⟩

private theorem min_ne_of_ne [LinearOrder α]
    {a b z : α} (h1 : a ≠ z) (h2 : b ≠ z) :
    min a b ≠ z := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

private theorem max_ne_of_ne [LinearOrder α]
    {a b z : α} (h1 : a ≠ z) (h2 : b ≠ z) :
    max a b ≠ z := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

/-- Sorting the two probed points leaves the inside-indicator sum
unchanged. -/
private theorem inside_sorted_sum [LinearOrder α]
    (l r a b : α) :
    ((if InsideChord l r (min a b) then (1 : ℕ) else 0) +
      (if InsideChord l r (max a b) then 1 else 0)) =
    ((if InsideChord l r a then (1 : ℕ) else 0) +
      (if InsideChord l r b then 1 else 0)) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, add_comm]

/-- The crossing indicator of a raw chord `{a, b}` against a third
chord `p` has the parity of the number of its raw ends inside
`p`. -/
private theorem cross_parity_raw [LinearOrder α]
    {p : α × α} {a b : α}
    (hab : a ≠ b) (h1a : a ≠ p.1) (h1b : b ≠ p.1)
    (h2a : a ≠ p.2) (h2b : b ≠ p.2) :
    (if ChordPairCross (min a b) (max a b) p.1 p.2 then (1 : ℕ)
      else 0) % 2 =
    ((if InsideChord p.1 p.2 a then (1 : ℕ) else 0) +
      (if InsideChord p.1 p.2 b then 1 else 0)) % 2 := by
  have h1 : (if ChordPairCross (min a b) (max a b) p.1 p.2
      then (1 : ℕ) else 0) =
      if ChordPairCross p.1 p.2 (min a b) (max a b) then 1
        else 0 :=
    if_congr chordPairCross_comm rfl rfl
  have h2 := chordPairCross_parity (x := p.1) (y := p.2)
    (min_lt_max.mpr hab) (min_ne_of_ne h1a h1b)
    (max_ne_of_ne h2a h2b)
  rw [h1, h2, inside_sorted_sum]

/-- The two cut-label inside-indicators against a chord avoiding
both cut labels sum (mod 2) to the crossing-the-cut indicator. -/
private theorem pair_cut_parity [LinearOrder α]
    {i j : α} (hij : i < j) {p : α × α}
    (hp12 : p.1 < p.2) (h1i : p.1 ≠ i) (h2j : p.2 ≠ j) :
    ((if InsideChord p.1 p.2 i then (1 : ℕ) else 0) +
      (if InsideChord p.1 p.2 j then 1 else 0)) % 2 =
      if CrossesCut i j p then 1 else 0 := by
  have hxor : CrossesCut i j p ↔
      Xor (InsideChord p.1 p.2 i) (InsideChord p.1 p.2 j) := by
    have e1 : CrossesCut i j (p.1, p.2) ↔
        ChordPairCross i j p.1 p.2 :=
      crossesCut_iff_chordPairCross hp12 h1i h2j
    have e2 : ChordPairCross p.1 p.2 i j ↔
        Xor (InsideChord p.1 p.2 i) (InsideChord p.1 p.2 j) :=
      chordPairCross_iff_xor hij (Ne.symm h1i) (Ne.symm h2j)
    exact e1.trans (chordPairCross_comm.trans e2)
  by_cases hI : InsideChord p.1 p.2 i <;>
    by_cases hJ : InsideChord p.1 p.2 j
  · rw [ite_eq_left hI, ite_eq_left hJ, ite_eq_right (fun hc =>
      ((hxor.mp hc).elim (fun h => h.2 hJ) (fun h => h.2 hI)))]
  · rw [ite_eq_left hI, ite_eq_right hJ,
      ite_eq_left (hxor.mpr (Or.inl ⟨hI, hJ⟩))]
  · rw [ite_eq_right hI, ite_eq_left hJ,
      ite_eq_left (hxor.mpr (Or.inr ⟨hJ, hI⟩))]
  · rw [ite_eq_right hI, ite_eq_right hJ, ite_eq_right (fun hc =>
      ((hxor.mp hc).elim (fun h => hI h.1) (fun h => hJ h.1)))]

/-- An entry of a sorted pair is one of the sorted values. -/
private theorem sorted_eq_cases [LinearOrder α]
    {a b c d : α}
    (he : (min a b, max a b) = (min c d, max c d)) :
    a = c ∨ a = d := by
  have h1 : min a b = min c d := congrArg Prod.fst he
  have h2 : max a b = max c d := congrArg Prod.snd he
  rcases le_total a b with hle | hle
  · rcases min_choice c d with h | h
    · exact Or.inl ((min_eq_left hle).symm.trans (h1.trans h))
    · exact Or.inr ((min_eq_left hle).symm.trans (h1.trans h))
  · rcases max_choice c d with h | h
    · exact Or.inl ((max_eq_left hle).symm.trans (h2.trans h))
    · exact Or.inr ((max_eq_left hle).symm.trans (h2.trans h))

/-! ## The system bridge -/

namespace EdgeSubset

end EdgeSubset

/-! ## The glue delta, crossing case -/

/-- **The glue delta, crossing case**: gluing the cut `{i, j}`
(`i < j`, chord `(i,x)` and chord `(j,y)` concatenating into
`(x,y)`, non-linked: `x ≠ j`) changes the diagram crossing count,
mod 2, by the number of surviving third chords crossing the cut
plus the mutual-crossing indicator of the two cut chords. -/
theorem diagCrossCount_glue_cross [LinearOrder α]
    {P : Finset (α × α)}
    (hP : IsChordDiagram P) {i j x y : α} (hij : i < j)
    (hxj : x ≠ j)
    (hi : (min i x, max i x) ∈ P) (hj : (min j y, max j y) ∈ P) :
    (diagCrossCount (glueChords i j P) + diagCrossCount P) % 2 =
      ((((P.erase (min i x, max i x)).erase
            (min j y, max j y)).filter (CrossesCut i j)).card +
        (if ChordPairCross (min i x) (max i x) (min j y) (max j y)
          then 1 else 0)) % 2 := by
  have hix : i ≠ x := min_lt_max.mp (hP.ordered _ hi)
  have hjy : j ≠ y := min_lt_max.mp (hP.ordered _ hj)
  have hCC : (min i x, max i x) ≠ (min j y, max j y) := by
    intro he
    rcases sorted_eq_cases he with h | h
    · exact ne_of_lt hij h
    · have he' : (min x i, max x i) = (min j y, max j y) := by
        rw [min_comm, max_comm]
        exact he
      rcases sorted_eq_cases he' with h' | h'
      · exact hxj h'
      · exact hix (h.trans h'.symm)
  have hrCi := ends_ne hP hj hi hCC
  have h1y : y ≠ min i x := Ne.symm hrCi.1.2
  have h2y : y ≠ max i x := Ne.symm hrCi.2.2
  have hxy : x ≠ y := Ne.symm (ne_ends_raw h1y h2y).2
  -- ═══════ PEELING THE TWO CUT CHORDS OFF THE DIAGRAM ═══════
  -- Above: the four ends are distinct and the two chords are two
  -- elements of the diagram.  Below: the count splits into their
  -- mutual crossing, their crossings with the rest, and the rest.
  have hCjE : (min j y, max j y) ∈ P.erase (min i x, max i x) :=
    Finset.mem_erase.mpr ⟨Ne.symm hCC, hj⟩
  have hCiQ : (min i x, max i x) ∉
      (P.erase (min i x, max i x)).erase (min j y, max j y) :=
    fun hm =>
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1 rfl
  have hCjQ : (min j y, max j y) ∉
      (P.erase (min i x, max i x)).erase (min j y, max j y) :=
    fun hm => (Finset.mem_erase.mp hm).1 rfl
  have hCiIns : (min i x, max i x) ∉ insert (min j y, max j y)
      ((P.erase (min i x, max i x)).erase (min j y, max j y)) := by
    intro hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact hCC h
    · exact hCiQ h
  have hPdec : insert (min i x, max i x) (insert (min j y, max j y)
      ((P.erase (min i x, max i x)).erase (min j y, max j y))) =
      P := by
    rw [Finset.insert_erase hCjE, Finset.insert_erase hi]
  have hnQ : (min x y, max x y) ∉
      (P.erase (min i x, max i x)).erase (min j y, max j y) := by
    intro hm
    have hmP : (min x y, max x y) ∈ P :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm)
    have hmne : (min x y, max x y) ≠ (min i x, max i x) :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
    have hr := ends_ne hP hi hmP hmne
    rcases le_total x y with h | h
    · exact hr.1.2 (min_eq_left h)
    · exact hr.2.2 (max_eq_left h)
  have hdG : diagCrossCount (glueChords i j P) =
      diagCrossCount
        ((P.erase (min i x, max i x)).erase (min j y, max j y)) +
      ∑ p ∈ (P.erase (min i x, max i x)).erase (min j y, max j y),
        (xInd (min x y, max x y) p + xInd p (min x y, max x y)) := by
    rw [glueChords_cross hP hxj hi hj, Finset.union_singleton,
      diagCrossCount_insert hnQ]
  have hdP : diagCrossCount (insert (min i x, max i x)
      (insert (min j y, max j y)
        ((P.erase (min i x, max i x)).erase (min j y, max j y)))) =
      diagCrossCount
        ((P.erase (min i x, max i x)).erase (min j y, max j y)) +
      (∑ p ∈ (P.erase (min i x, max i x)).erase (min j y, max j y),
        (xInd (min j y, max j y) p + xInd p (min j y, max j y))) +
      ((xInd (min i x, max i x) (min j y, max j y) +
        xInd (min j y, max j y) (min i x, max i x)) +
       ∑ p ∈ (P.erase (min i x, max i x)).erase (min j y, max j y),
        (xInd (min i x, max i x) p + xInd p (min i x, max i x))) := by
    rw [diagCrossCount_insert hCiIns, diagCrossCount_insert hCjQ,
      Finset.sum_insert hCjQ]
  rw [hPdec] at hdP
  have hd := hP.disjoint _ hi _ hj hCC
  have hM : xInd (min i x, max i x) (min j y, max j y) +
      xInd (min j y, max j y) (min i x, max i x) =
      if ChordPairCross (min i x) (max i x) (min j y) (max j y)
        then 1 else 0 :=
    xInd_pair hd.fst_ne_fst
  have hthird : (∑ p ∈ (P.erase (min i x, max i x)).erase
        (min j y, max j y),
      ((xInd (min x y, max x y) p + xInd p (min x y, max x y)) +
        ((xInd (min j y, max j y) p + xInd p (min j y, max j y)) +
         (xInd (min i x, max i x) p +
          xInd p (min i x, max i x))))) % 2 =
      (((P.erase (min i x, max i x)).erase
          (min j y, max j y)).filter (CrossesCut i j)).card % 2 := by
    rw [Finset.sum_nat_mod, Finset.card_filter]
    refine congrArg (· % 2) (Finset.sum_congr rfl fun p hp => ?_)
    have hpP : p ∈ P :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
    have hpCj : p ≠ (min j y, max j y) := Finset.ne_of_mem_erase hp
    have hpCi : p ≠ (min i x, max i x) :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hp)
    have hri := ends_ne hP hi hpP hpCi
    have hrj := ends_ne hP hj hpP hpCj
    have hp12 : p.1 < p.2 := hP.ordered p hpP
    have e_n : xInd (min x y, max x y) p +
        xInd p (min x y, max x y) =
        if ChordPairCross (min x y) (max x y) p.1 p.2 then 1
          else 0 :=
      xInd_pair (min_ne_of_ne (Ne.symm hri.1.2) (Ne.symm hrj.1.2))
    have e_j : xInd (min j y, max j y) p +
        xInd p (min j y, max j y) =
        if ChordPairCross (min j y) (max j y) p.1 p.2 then 1
          else 0 :=
      xInd_pair (min_ne_of_ne (Ne.symm hrj.1.1) (Ne.symm hrj.1.2))
    have e_i : xInd (min i x, max i x) p +
        xInd p (min i x, max i x) =
        if ChordPairCross (min i x) (max i x) p.1 p.2 then 1
          else 0 :=
      xInd_pair (min_ne_of_ne (Ne.symm hri.1.1) (Ne.symm hri.1.2))
    rw [e_n, e_j, e_i]
    have h_i := cross_parity_raw hix (Ne.symm hri.1.1)
      (Ne.symm hri.1.2) (Ne.symm hri.2.1) (Ne.symm hri.2.2)
    have h_j := cross_parity_raw hjy (Ne.symm hrj.1.1)
      (Ne.symm hrj.1.2) (Ne.symm hrj.2.1) (Ne.symm hrj.2.2)
    have h_n := cross_parity_raw hxy (Ne.symm hri.1.2)
      (Ne.symm hrj.1.2) (Ne.symm hri.2.2) (Ne.symm hrj.2.2)
    have h_cut := pair_cut_parity hij hp12 hri.1.1 hrj.2.1
    omega
  have hsplit : (∑ p ∈ (P.erase (min i x, max i x)).erase
        (min j y, max j y),
      ((xInd (min x y, max x y) p + xInd p (min x y, max x y)) +
        ((xInd (min j y, max j y) p + xInd p (min j y, max j y)) +
         (xInd (min i x, max i x) p +
          xInd p (min i x, max i x))))) =
      (∑ p ∈ (P.erase (min i x, max i x)).erase (min j y, max j y),
        (xInd (min x y, max x y) p + xInd p (min x y, max x y))) +
      ((∑ p ∈ (P.erase (min i x, max i x)).erase (min j y, max j y),
        (xInd (min j y, max j y) p + xInd p (min j y, max j y))) +
       (∑ p ∈ (P.erase (min i x, max i x)).erase (min j y, max j y),
        (xInd (min i x, max i x) p + xInd p (min i x, max i x)))) := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit] at hthird
  rw [hdG, hdP]
  omega

end RS
