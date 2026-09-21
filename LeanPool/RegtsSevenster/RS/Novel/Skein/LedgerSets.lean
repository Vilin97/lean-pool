/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StateFlipSet
import LeanPool.RegtsSevenster.RS.Novel.Skein.StatusSet

/-!
# Relabel sets for the canonical ledgers

A canonical ledger reports the state it lands in as
`stateOddFlipSet st E`.  This module is the arithmetic of the set
`E`: it is a symmetric-difference fold (`pairFold`) of label pairs,
one pair per flipped chain, each pair the two end labels of a chord
of the stage system.  Within one recanonicalization the flipped
chains are distinct anti-canonical chains (`AntiLowPair`), so the
pairs are pairwise disjoint (`PairDisjoint`) and the fold is a
disjoint union (`mem_pairFold_of_pairwise`).

The accumulated relabel of a whole route is the status difference
`statusDiff`, which telescopes along chains (`statusDiff_trans`)
and vanishes on a pairing-preserving one
(`statusDiff_of_samePairing`).
-/

namespace RS

open scoped Classical

section PairSets

variable {k ℓ : ℕ} {α : Type}

/-- Symmetric difference of two finite sets — the composition law
of `stateOddFlipSet` (`stateOddFlipSet_symmU`). -/
noncomputable def symmU (E₁ E₂ : Finset α) : Finset α :=
  (E₁ \ E₂) ∪ (E₂ \ E₁)

/-- Membership in a symmetric difference: in exactly one of the
two sets. -/
theorem mem_symmU {E₁ E₂ : Finset α} {i : α} :
    i ∈ symmU E₁ E₂ ↔
      (i ∈ E₁ ∧ i ∉ E₂) ∨ (i ∈ E₂ ∧ i ∉ E₁) := by
  unfold symmU
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]

/-- The symmetric difference of a set with itself is empty. -/
theorem symmU_self (A : Finset α) : symmU A A = ∅ := by
  apply Finset.ext
  intro i
  rw [mem_symmU]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact absurd h1 h2
  · intro h
    exact absurd h (Finset.notMem_empty i)

/-- **Telescoping**: symmetric differences against a common middle
compose. -/
theorem symmU_trans (A B C : Finset α) :
    symmU (symmU A B) (symmU B C) = symmU A C := by
  apply Finset.ext
  intro i
  rw [mem_symmU, mem_symmU, mem_symmU, mem_symmU]
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    by_cases hC : i ∈ C <;> tauto

/-- The empty set is a left unit. -/
theorem symmU_empty_left (E : Finset α) : symmU ∅ E = E := by
  apply Finset.ext
  intro i
  rw [mem_symmU]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h (Finset.notMem_empty i)
    · exact h
  · intro h
    exact Or.inr ⟨h, Finset.notMem_empty i⟩

/-- Symmetric difference is associative, so a fold over a list is
well-behaved. -/
theorem symmU_assoc (E₁ E₂ E₃ : Finset α) :
    symmU (symmU E₁ E₂) E₃ = symmU E₁ (symmU E₂ E₃) := by
  apply Finset.ext
  intro i
  rw [mem_symmU, mem_symmU, mem_symmU, mem_symmU]
  tauto

/-- The two-element label set of a label pair. -/
noncomputable def pairSet (p : α × α) : Finset α := {p.1, p.2}

/-- Membership in a pair's label set. -/
theorem mem_pairSet {p : α × α} {i : α} :
    i ∈ pairSet p ↔ i = p.1 ∨ i = p.2 := by
  unfold pairSet
  rw [Finset.mem_insert, Finset.mem_singleton]

/-- The symmetric-difference fold of a list of label pairs. -/
noncomputable def pairFold (L : List (α × α)) : Finset α :=
  L.foldr (fun p E => symmU (pairSet p) E) ∅

/-- The fold over no pairs is empty: nothing relabelled. -/
theorem pairFold_nil : pairFold ([] : List (α × α)) = ∅ := rfl

/-- One more pair contributes its two labels, cancelling any that
the rest of the fold already carries. -/
theorem pairFold_cons (p : α × α) (L : List (α × α)) :
    pairFold (p :: L) = symmU (pairSet p) (pairFold L) := rfl

/-- The fold turns concatenation into symmetric difference — the
composition law the accumulated relabel needs. -/
theorem pairFold_append (L₁ L₂ : List (α × α)) :
    pairFold (L₁ ++ L₂) = symmU (pairFold L₁) (pairFold L₂) := by
  induction L₁ with
  | nil =>
    rw [List.nil_append, pairFold_nil, symmU_empty_left]
  | cons p L ih =>
    rw [List.cons_append, pairFold_cons, pairFold_cons, ih,
      symmU_assoc]

/-- **The fold of pairwise disjoint pairs is their union**: under
`PairDisjoint` no cancellation occurs, so membership in the fold is
membership in some pair. -/
theorem mem_pairFold_of_pairwise {L : List (α × α)}
    (hL : L.Pairwise PairDisjoint) {i : α} :
    i ∈ pairFold L ↔ ∃ p ∈ L, i = p.1 ∨ i = p.2 := by
  induction L with
  | nil =>
    rw [pairFold_nil]
    constructor
    · intro h
      exact absurd h (Finset.notMem_empty i)
    · rintro ⟨p, hp, -⟩
      cases hp
  | cons p L ih =>
    obtain ⟨hd, htl⟩ := List.pairwise_cons.mp hL
    rw [pairFold_cons, mem_symmU, mem_pairSet, ih htl]
    constructor
    · rintro (⟨h1, -⟩ | ⟨⟨q, hq, hiq⟩, -⟩)
      · exact ⟨p, List.mem_cons.mpr (Or.inl rfl), h1⟩
      · exact ⟨q, List.mem_cons.mpr (Or.inr hq), hiq⟩
    · rintro ⟨q, hq, hiq⟩
      rcases List.mem_cons.mp hq with rfl | hq'
      · refine Or.inl ⟨hiq, ?_⟩
        rintro ⟨q', hq', hiq'⟩
        have hdisj := hd q' hq'
        rcases hiq with h1 | h1 <;> rcases hiq' with h2 | h2
        · exact hdisj.fst_ne_fst (h1.symm.trans h2)
        · exact hdisj.fst_ne_snd (h1.symm.trans h2)
        · exact hdisj.snd_ne_fst (h1.symm.trans h2)
        · exact hdisj.snd_ne_snd (h1.symm.trans h2)
      · refine Or.inr ⟨⟨q, hq', hiq⟩, ?_⟩
        have hdisj := hd q hq'
        rintro (h1 | h1) <;> rcases hiq with h2 | h2
        · exact hdisj.fst_ne_fst (h1.symm.trans h2)
        · exact hdisj.fst_ne_snd (h1.symm.trans h2)
        · exact hdisj.snd_ne_fst (h1.symm.trans h2)
        · exact hdisj.snd_ne_snd (h1.symm.trans h2)

/-! ## Set relabels: boundary matching and composition -/

/-- Composition of set relabels is the `symmU` of the sets. -/
theorem stateOddFlipSet_symmU {st : GenBoundaryState k ℓ α}
    (E₁ E₂ : Finset α) :
    stateOddFlipSet (stateOddFlipSet st E₁) E₂ =
      stateOddFlipSet st (symmU E₁ E₂) :=
  stateOddFlipSet_flipSet E₁ E₂

end PairSets

namespace EdgeSubset

variable {α : Type}

/-! ## Anti-canonical chain pairs -/

/-- A chord pair whose low end is anti-canonical for `o`: the label
pair of a chain flipped by the recanonicalization of `o`. -/
def AntiLowPair [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (p : α × α) : Prop :=
  ∃ (β : W.Flag) (hβ : β ∈ F.boundaryFlags),
    β ∈ antiLowSet o ∧
    p.1 = F.boundaryLabel hβ ∧
    p.2 = F.boundaryLabel (κ.pathMatch_mem hβ)

/-- An anti-low pair is ordered: low label first. -/
theorem AntiLowPair.lt [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {p : α × α} (h : AntiLowPair o p) :
    p.1 < p.2 := by
  obtain ⟨β, hβ, hm, h1, h2⟩ := h
  obtain ⟨hβ', -, hlow, -⟩ := mem_antiLowSet.mp hm
  rw [h1, h2]
  exact hlow

/-- Anti-canonical pairs survive enlarging the anti-canonical
set. -/
theorem AntiLowPair.mono [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o o' : κ.Orientation}
    (hsub : antiLowSet o' ⊆ antiLowSet o) {p : α × α}
    (h : AntiLowPair o' p) : AntiLowPair o p := by
  obtain ⟨β, hβ, hm, h1, h2⟩ := h
  exact ⟨β, hβ, hsub hm, h1, h2⟩

/-- **Distinct anti-canonical chains have disjoint label pairs**:
the low ends are distinct low ends, so no end of one chord can be
an end of the other. -/
theorem antiLowPair_disjoint [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {β γ : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (hγ : γ ∈ F.boundaryFlags)
    (hβm : β ∈ antiLowSet o) (hγm : γ ∈ antiLowSet o)
    (hne : β ≠ γ) :
    PairDisjoint
      (F.boundaryLabel hβ, F.boundaryLabel (κ.pathMatch_mem hβ))
      (F.boundaryLabel hγ, F.boundaryLabel (κ.pathMatch_mem hγ)) := by
  obtain ⟨hβ', hintβ, hlowβ, -⟩ := mem_antiLowSet.mp hβm
  obtain ⟨hγ', hintγ, hlowγ, -⟩ := mem_antiLowSet.mp hγm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    exact hne (boundaryLabel_inj hβ hγ he)
  · intro he
    exact low_ne_pathMatch_of_low hγ hβ hlowγ hlowβ
      (boundaryLabel_inj hβ (κ.pathMatch_mem hγ) he)
  · intro he
    exact low_ne_pathMatch_of_low hβ hγ hlowβ hlowγ
      (boundaryLabel_inj (κ.pathMatch_mem hβ) hγ he).symm
  · intro he
    have h1 : κ.pathMatch β hβ = κ.pathMatch γ hγ :=
      boundaryLabel_inj (κ.pathMatch_mem hβ)
        (κ.pathMatch_mem hγ) he
    apply hne
    calc β = κ.pathMatch (κ.pathMatch β hβ)
          (κ.pathMatch_mem hβ) := (κ.pathMatch_invol hβ).symm
      _ = κ.pathMatch (κ.pathMatch γ hγ)
          (κ.pathMatch_mem hγ) :=
        κ.pathMatch_congr h1 (κ.pathMatch_mem hβ)
          (κ.pathMatch_mem hγ)
      _ = γ := κ.pathMatch_invol hγ

end EdgeSubset

namespace EdgeSubset

variable {W : Fragment α} {F : EdgeSubset W}

/-- The status difference of two systems: the labels whose
high-status differs — the potential of the canonical route's
accumulated relabel. -/
noncomputable def statusDiff [LinearOrder α]
    (κ κ' : F.RelTransitionSystem) : Finset α :=
  symmU (highSet κ) (highSet κ')

/-- A system differs from itself nowhere: the relabel accumulated
along a trivial route is empty. -/
theorem statusDiff_self [LinearOrder α]
    (κ : F.RelTransitionSystem) : statusDiff κ κ = ∅ :=
  symmU_self _

/-- The status difference telescopes along chains. -/
theorem statusDiff_trans [LinearOrder α]
    (κ₁ κ₂ κ₃ : F.RelTransitionSystem) :
    symmU (statusDiff κ₁ κ₂) (statusDiff κ₂ κ₃) =
      statusDiff κ₁ κ₃ :=
  symmU_trans _ _ _

/-- Same-pairing endpoints have empty status difference. -/
theorem statusDiff_of_samePairing [LinearOrder α]
    {κ κ' : F.RelTransitionSystem} (h : SamePairing κ κ') :
    statusDiff κ κ' = ∅ := by
  unfold statusDiff
  rw [highSet_of_samePairing h]
  exact symmU_self _

end EdgeSubset

/-- Propositional inequality as an exclusive disjunction, in the
`symmU` component order. -/
theorem prop_ne_cases {P Q : Prop} (h : P ≠ Q) :
    (P ∧ ¬Q) ∨ (¬P ∧ Q) := by
  by_cases hP : P
  · by_cases hQ : Q
    · exact absurd (propext (iff_of_true hP hQ)) h
    · exact Or.inl ⟨hP, hQ⟩
  · by_cases hQ : Q
    · exact Or.inr ⟨hP, hQ⟩
    · exact absurd (propext (iff_of_false hP hQ)) h

/-- One holds and the other does not, so they differ. -/
theorem prop_ne_of_left {P Q : Prop} (hP : P) (hQ : ¬Q) :
    P ≠ Q := by
  intro h
  rw [h] at hP
  exact hQ hP

/-- The mirrored case. -/
theorem prop_ne_of_right {P Q : Prop} (hP : ¬P) (hQ : Q) :
    P ≠ Q := by
  intro h
  rw [← h] at hQ
  exact hP hQ

end RS
