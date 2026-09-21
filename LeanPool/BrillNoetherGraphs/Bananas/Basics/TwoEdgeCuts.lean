/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaGeometry

/-!
# Two-edge cuts of a banana

The elementary but important first part of the `SameStrand` geometry: a cut
which separates the two multivalent endpoints must cross every strand.  Hence
a two-edge cut in a genus-at-least-two banana leaves the endpoints on the
same side.  The remaining interval classification is deliberately kept
separate from this cardinality fact.
-/

namespace Bananas

open Utilities

open Utilities Finset
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

private theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

private theorem four_le_card_of_four_mem {X : Type} [DecidableEq X]
    {s : Finset X} {a b c d : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) :
    4 ≤ s.card := by
  have hsub : ({a, b, c, d} : Finset X) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  calc
    4 = ({a, b, c, d} : Finset X).card := by
      simp [hab, hac, had, hbc, hbd, hcd]
    _ ≤ s.card := Finset.card_le_card hsub

private theorem three_le_card_of_three_mem {X : Type} [DecidableEq X]
    {s : Finset X} {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset X) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  calc
    3 = ({a, b, c} : Finset X).card := by simp [hab, hac, hbc]
    _ ≤ s.card := Finset.card_le_card hsub

/-- If a cut separates the two core vertices of a banana, it has at least one
crossing unit step on each strand. -/
theorem strands_le_crossingSteps_of_core_separated {g : ℕ} (B : Banana g)
    (A : Finset B.graph.V)
    (hSep : (B.coreVertex (0 : Fin 2) ∈ A ∧ B.coreVertex (1 : Fin 2) ∉ A) ∨
      (B.coreVertex (0 : Fin 2) ∉ A ∧ B.coreVertex (1 : Fin 2) ∈ A)) :
    g + 1 ≤ (B.crossingSteps A).card := by
  classical
  have hCrosses (edge : Fin (g + 1)) :
      (B.pathVertex edge ⟨0, by omega⟩ ∈ A ∧
        B.pathVertex edge ⟨B.length edge, by omega⟩ ∉ A) ∨
      (B.pathVertex edge ⟨0, by omega⟩ ∉ A ∧
        B.pathVertex edge ⟨B.length edge, by omega⟩ ∈ A) := by
    rw [B.pathVertex_zero, B.pathVertex_length]
    rcases hSep with hSep | hSep
    · rcases fin_two_cases (B.core.tail edge) with hTail | hTail <;>
        rcases fin_two_cases (B.core.head edge) with hHead | hHead
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
      · exact Or.inl ⟨by simpa [hTail] using hSep.1,
          by simpa [hHead] using hSep.2⟩
      · exact Or.inr ⟨by simpa [hTail] using hSep.2,
          by simpa [hHead] using hSep.1⟩
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
    · rcases fin_two_cases (B.core.tail edge) with hTail | hTail <;>
        rcases fin_two_cases (B.core.head edge) with hHead | hHead
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
      · exact Or.inr ⟨by simpa [hTail] using hSep.1,
          by simpa [hHead] using hSep.2⟩
      · exact Or.inl ⟨by simpa [hTail] using hSep.2,
          by simpa [hHead] using hSep.1⟩
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
  choose offset hOffset using fun edge =>
    B.exists_crossingStep_between A edge
      ⟨0, by omega⟩ ⟨B.length edge, by omega⟩
      (by have := B.length_pos edge; omega) (hCrosses edge)
  have hMaps : ∀ edge : Fin (g + 1),
      (⟨edge, offset edge⟩ : B.Step) ∈ B.crossingSteps A := fun edge =>
    (hOffset edge).2.2
  have hInj : Set.InjOn (fun edge : Fin (g + 1) =>
      (⟨edge, offset edge⟩ : B.Step))
      ↑(Finset.univ : Finset (Fin (g + 1))) := by
    intro e₁ _ e₂ _ hEq
    exact congrArg Sigma.fst hEq
  have hCard : (Finset.univ : Finset (Fin (g + 1))).card ≤
      (B.crossingSteps A).card := Finset.card_le_card_of_injOn
    (fun edge : Fin (g + 1) => (⟨edge, offset edge⟩ : B.Step))
    (fun edge _ => hMaps edge) hInj
  simpa using hCard

/-- A two-edge cut in a banana with at least three strands cannot separate its
two core vertices.  This is the global half of the two-edge-cut
classification used in the reduced-divisor argument. -/
theorem core_vertices_same_side_of_cutMultiplicity_two {g : ℕ}
    (hg : 2 ≤ g) (B : Banana g) (A : Finset B.graph.V)
    (hCut : cutMultiplicity B.graph A = 2) :
    (B.coreVertex (0 : Fin 2) ∈ A ↔ B.coreVertex (1 : Fin 2) ∈ A) := by
  by_contra hDifferent
  push Not at hDifferent
  have hSep : (B.coreVertex (0 : Fin 2) ∈ A ∧ B.coreVertex (1 : Fin 2) ∉ A) ∨
      (B.coreVertex (0 : Fin 2) ∉ A ∧ B.coreVertex (1 : Fin 2) ∈ A) := by
    tauto
  have hStrands := strands_le_crossingSteps_of_core_separated B A hSep
  have hCount : ((B.crossingSteps A).card : ℤ) = 2 := by
    rw [← B.cutMultiplicity_eq_card_crossingSteps A]
    exact hCut
  have hStrandsInt : (g + 1 : ℤ) ≤ ((B.crossingSteps A).card : ℤ) := by
    exact_mod_cast hStrands
  omega

/-- If both core vertices lie outside a cut and the cut contains internal
vertices on two different strands, then each strand must be entered and left.
The resulting four crossing steps are distinct. -/
theorem four_le_crossingSteps_of_two_interior_strands {g : ℕ} (B : Banana g)
    (A : Finset B.graph.V) (α β : Fin (g + 1)) (hαβ : α ≠ β)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (hZero : B.coreVertex (0 : Fin 2) ∉ A)
    (hOne : B.coreVertex (1 : Fin 2) ∉ A)
    (hiA : B.pathVertex α i ∈ A) (hjA : B.pathVertex β j ∈ A) :
    4 ≤ (B.crossingSteps A).card := by
  classical
  have hTailOut : ∀ edge : Fin (g + 1), B.coreVertex (B.core.tail edge) ∉ A := by
    intro edge
    rcases fin_two_cases (B.core.tail edge) with h | h
    · simpa [h] using hZero
    · simpa [h] using hOne
  have hHeadOut : ∀ edge : Fin (g + 1), B.coreVertex (B.core.head edge) ∉ A := by
    intro edge
    rcases fin_two_cases (B.core.head edge) with h | h
    · simpa [h] using hZero
    · simpa [h] using hOne
  obtain ⟨a, haLo, haHi, ha⟩ := B.exists_crossingStep_between A α
    ⟨0, by omega⟩ i (by exact hi.1) (by
      right
      exact ⟨by rw [B.pathVertex_zero]; exact hTailOut α, hiA⟩)
  obtain ⟨b, hbLo, hbHi, hb⟩ := B.exists_crossingStep_between A α i
    ⟨B.length α, by omega⟩ (by exact hi.2) (by
      left
      exact ⟨hiA, by simpa using hHeadOut α⟩)
  obtain ⟨c, hcLo, hcHi, hc⟩ := B.exists_crossingStep_between A β
    ⟨0, by omega⟩ j (by exact hj.1) (by
      right
      exact ⟨by rw [B.pathVertex_zero]; exact hTailOut β, hjA⟩)
  obtain ⟨d, hdLo, hdHi, hd⟩ := B.exists_crossingStep_between A β j
    ⟨B.length β, by omega⟩ (by exact hj.2) (by
      left
      exact ⟨hjA, by simpa using hHeadOut β⟩)
  apply four_le_card_of_four_mem
    (a := (⟨α, a⟩ : B.Step)) (b := (⟨α, b⟩ : B.Step))
    (c := (⟨β, c⟩ : B.Step)) (d := (⟨β, d⟩ : B.Step))
  · intro hEq
    have : a.val = b.val := congrArg (fun s : B.Step => s.2.val) hEq
    omega
  · intro hEq
    exact hαβ (congrArg Sigma.fst hEq)
  · intro hEq
    exact hαβ (congrArg Sigma.fst hEq)
  · intro hEq
    exact hαβ (congrArg Sigma.fst hEq)
  · intro hEq
    exact hαβ (congrArg Sigma.fst hEq)
  · intro hEq
    have : c.val = d.val := congrArg (fun s : B.Step => s.2.val) hEq
    omega
  · exact ha
  · exact hb
  · exact hc
  · exact hd

/-- Consequently, a two-edge cut whose endpoints are both outside can contain
interior vertices from at most one strand. -/
theorem interior_strands_eq_of_cutMultiplicity_two_endpoints_outside
    {g : ℕ} (B : Banana g) (A : Finset B.graph.V)
    (hCut : cutMultiplicity B.graph A = 2)
    (hZero : B.coreVertex (0 : Fin 2) ∉ A)
    (hOne : B.coreVertex (1 : Fin 2) ∉ A)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (hiA : B.pathVertex α i ∈ A) (hjA : B.pathVertex β j ∈ A) :
    α = β := by
  by_contra hαβ
  have hFour := four_le_crossingSteps_of_two_interior_strands B A α β hαβ
    i j hi hj hZero hOne hiA hjA
  have hCount : ((B.crossingSteps A).card : ℤ) = 2 := by
    rw [← B.cutMultiplicity_eq_card_crossingSteps A]
    exact hCut
  have hFourInt : (4 : ℤ) ≤ ((B.crossingSteps A).card : ℤ) := by
    exact_mod_cast hFour
  omega

/-- Once two distinct crossing steps on strand `α` exhaust a two-edge cut,
no other strand can cross that cut. -/
theorem crossing_step_on_designated_strand_of_cutMultiplicity_two
    {g : ℕ} (B : Banana g) (A : Finset B.graph.V) (α : Fin (g + 1))
    (a b : Fin (B.length α)) (hab : a ≠ b)
    (ha : (⟨α, a⟩ : B.Step) ∈ B.crossingSteps A)
    (hb : (⟨α, b⟩ : B.Step) ∈ B.crossingSteps A)
    (hCut : cutMultiplicity B.graph A = 2)
    (step : B.Step) (hStep : step ∈ B.crossingSteps A) : step.1 = α := by
  by_contra hNot
  have hStepA : step ≠ (⟨α, a⟩ : B.Step) := by
    intro h
    exact hNot (congrArg Sigma.fst h)
  have hStepB : step ≠ (⟨α, b⟩ : B.Step) := by
    intro h
    exact hNot (congrArg Sigma.fst h)
  have habStep : (⟨α, a⟩ : B.Step) ≠ ⟨α, b⟩ := by
    intro h
    apply hab
    apply Fin.ext
    exact congrArg (fun s : B.Step => s.2.val) h
  have hThree : 3 ≤ (B.crossingSteps A).card :=
    three_le_card_of_three_mem habStep (Ne.symm hStepA) (Ne.symm hStepB) ha hb hStep
  have hCount : (B.crossingSteps A).card = 2 := by
    exact_mod_cast (B.cutMultiplicity_eq_card_crossingSteps A).symm.trans hCut
  omega

/-- The local interval form of a two-edge cut.  If two distinct steps of
strand `α` account for a cut of multiplicity two, every other strand is
constant on the cut: all its path vertices have the tail's membership. -/
theorem other_strands_constant_of_cutMultiplicity_two
    {g : ℕ} (B : Banana g) (A : Finset B.graph.V) (α β : Fin (g + 1))
    (hαβ : α ≠ β) (a b : Fin (B.length α)) (hab : a ≠ b)
    (ha : (⟨α, a⟩ : B.Step) ∈ B.crossingSteps A)
    (hb : (⟨α, b⟩ : B.Step) ∈ B.crossingSteps A)
    (hCut : cutMultiplicity B.graph A = 2)
    (z : B.PathPosition β) :
    B.pathVertex β z ∈ A ↔ B.coreVertex (B.core.tail β) ∈ A := by
  constructor
  · intro hz
    by_contra hTail
    by_cases hzZero : z.val = 0
    · have hEq : z = ⟨0, by omega⟩ := by apply Fin.ext; exact hzZero
      rw [hEq, B.pathVertex_zero] at hz
      exact hTail hz
    · have hPositive : 0 < z.val := Nat.pos_of_ne_zero hzZero
      obtain ⟨offset, _, _, hCross⟩ := B.exists_crossingStep_between A β
        ⟨0, by omega⟩ z hPositive (Or.inr ⟨by
          rw [B.pathVertex_zero]
          exact hTail, hz⟩)
      have hEdge := crossing_step_on_designated_strand_of_cutMultiplicity_two
        B A α a b hab ha hb hCut ⟨β, offset⟩ hCross
      exact hαβ hEdge.symm
  · intro hTail
    by_contra hz
    by_cases hzZero : z.val = 0
    · have hEq : z = ⟨0, by omega⟩ := by apply Fin.ext; exact hzZero
      rw [hEq, B.pathVertex_zero] at hz
      exact hz hTail
    · have hPositive : 0 < z.val := Nat.pos_of_ne_zero hzZero
      obtain ⟨offset, _, _, hCross⟩ := B.exists_crossingStep_between A β
        ⟨0, by omega⟩ z hPositive (Or.inl ⟨by
          rw [B.pathVertex_zero]
          exact hTail, hz⟩)
      have hEdge := crossing_step_on_designated_strand_of_cutMultiplicity_two
        B A α a b hab ha hb hCut ⟨β, offset⟩ hCross
      exact hαβ hEdge.symm

/-! ## Membership propagation along a strand -/

/-- If no unit step of a strand crosses a cut between two positions, the cut
membership is constant at those positions.  This is the induction principle
needed to turn the two crossing steps of a multiplicity-two cut into an
interval on the designated strand. -/
theorem pathVertex_mem_iff_of_no_crossing_between
    {g : ℕ} (B : Banana g) (A : Finset B.graph.V)
    (α : Fin (g + 1)) (lo hi : B.PathPosition α) (hlt : lo.val < hi.val)
    (hNo : ∀ offset : Fin (B.length α),
      lo.val ≤ offset.val → offset.val < hi.val →
      (⟨α, offset⟩ : B.Step) ∉ B.crossingSteps A) :
    (B.pathVertex α lo ∈ A ↔ B.pathVertex α hi ∈ A) := by
  constructor
  · intro hLo
    by_contra hHi
    obtain ⟨offset, hLoOffset, hHiOffset, hCross⟩ :=
      B.exists_crossingStep_between A α lo hi hlt
        (Or.inl ⟨hLo, hHi⟩)
    exact hNo offset hLoOffset hHiOffset hCross
  · intro hHi
    by_contra hLo
    obtain ⟨offset, hLoOffset, hHiOffset, hCross⟩ :=
      B.exists_crossingStep_between A α lo hi hlt
        (Or.inr ⟨hLo, hHi⟩)
    exact hNo offset hLoOffset hHiOffset hCross

/-- Under a multiplicity-two cut, two distinct crossing steps on one strand
exhaust all crossings on that strand. -/
theorem no_other_crossing_step_on_designated_strand_of_cutMultiplicity_two
    {g : ℕ} (B : Banana g) (A : Finset B.graph.V) (α : Fin (g + 1))
    (a b : Fin (B.length α)) (hab : a ≠ b)
    (ha : (⟨α, a⟩ : B.Step) ∈ B.crossingSteps A)
    (hb : (⟨α, b⟩ : B.Step) ∈ B.crossingSteps A)
    (hCut : cutMultiplicity B.graph A = 2)
    (c : Fin (B.length α))
    (hc : (⟨α, c⟩ : B.Step) ∈ B.crossingSteps A) :
    c = a ∨ c = b := by
  have hα := crossing_step_on_designated_strand_of_cutMultiplicity_two
    B A α a b hab ha hb hCut (⟨α, c⟩ : B.Step) hc
  have hCard : (B.crossingSteps A).card = 2 := by
    exact_mod_cast (B.cutMultiplicity_eq_card_crossingSteps A).symm.trans hCut
  by_cases hca : c = a
  · exact Or.inl hca
  by_cases hcb : c = b
  · exact Or.inr hcb
  have hStepA : (⟨α, a⟩ : B.Step) ≠ ⟨α, c⟩ := by
    intro h
    apply hca
    apply Fin.ext
    exact (congrArg (fun s : B.Step => s.2.val) h).symm
  have hStepB : (⟨α, b⟩ : B.Step) ≠ ⟨α, c⟩ := by
    intro h
    apply hcb
    apply Fin.ext
    exact (congrArg (fun s : B.Step => s.2.val) h).symm
  have hThree : 3 ≤ (B.crossingSteps A).card :=
    three_le_card_of_three_mem
      (by
        intro h
        apply hab
        apply Fin.ext
        exact congrArg (fun s : B.Step => s.2.val) h)
      hStepA hStepB ha hb hc
  omega

/-- Between the two crossing steps of a multiplicity-two cut, membership on
the designated strand is constant.  The statement is oriented from the
vertex immediately after the first crossing to any later position through
the second crossing. -/
theorem pathVertex_mem_eq_after_first_crossing_before_second
    {g : ℕ} (B : Banana g) (A : Finset B.graph.V) (α : Fin (g + 1))
    (a b : Fin (B.length α)) (hab : a.val < b.val)
    (ha : (⟨α, a⟩ : B.Step) ∈ B.crossingSteps A)
    (hb : (⟨α, b⟩ : B.Step) ∈ B.crossingSteps A)
    (hCut : cutMultiplicity B.graph A = 2)
    (x : B.PathPosition α) (hax : a.val < x.val) (hxb : x.val ≤ b.val) :
    (B.pathVertex α ⟨a.val + 1, by omega⟩ ∈ A ↔
      B.pathVertex α x ∈ A) := by
  by_cases hEq : x.val = a.val + 1
  · have hx : x = ⟨a.val + 1, by omega⟩ := by
      apply Fin.ext
      exact hEq
    rw [hx]
  · have hLo : a.val + 1 < x.val := by omega
    apply pathVertex_mem_iff_of_no_crossing_between B A α
      ⟨a.val + 1, by omega⟩ x hLo
    intro c hcLo hcHi hCross
    have hcLo' : a.val + 1 ≤ c.val := by simpa using hcLo
    have hcHi' : c.val < x.val := hcHi
    have hca : c ≠ a := by
      intro h
      subst c
      omega
    have hcb : c ≠ b := by
      intro h
      subst c
      omega
    have hcCases := no_other_crossing_step_on_designated_strand_of_cutMultiplicity_two
      B A α a b (by omega) ha hb hCut c hCross
    rcases hcCases with hc | hc
    · exact (hca hc).elim
    · exact (hcb hc).elim

end Bananas
