/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
module

public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Combinatorics.Matroid.Rank.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max


/-!
  The NBC cancellation is first proved at the level of a finite matroid.  The
  graphic specialization only needs the standard cycle-matroid interface:
  spanning edge sets are the connected subgraphs and circuits are graph cycles.
  Keeping this layer independent makes the cancellation proof auditable and
  avoids hiding it behind a library theorem.
 -/

@[expose] public section

namespace HsVirial

open Set
open scoped BigOperators



variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- The ground set of a matroid on a finite ambient type, as a finite set. -/
noncomputable def matroidGround (M : Matroid α) : Finset α := by
  classical
  exact Finset.univ.filter (fun e => e ∈ M.E)

omit [DecidableEq α] [LinearOrder α] in
lemma mem_matroidGround (M : Matroid α) (e : α) :
    e ∈ matroidGround M ↔ e ∈ M.E := by
  simp [matroidGround]

/-- An element completing a circuit whose other elements lie in the specified set. -/
def IsNBCandidate (M : Matroid α) (A : Finset α) (e : α) : Prop :=
  ∃ C : Finset α,
    M.IsCircuit (C : Set α) ∧
    e ∈ C ∧
    (∀ f ∈ C, f ≤ e) ∧
    ((C.erase e : Finset α) : Set α) ⊆ (A : Set α)

/-- The possible circuit-completing elements used by the cancellation involution. -/
noncomputable def nbcCandidates (M : Matroid α) (A : Finset α) : Finset α := by
  classical
  exact (matroidGround M).filter (IsNBCandidate M A)

/-- The set has at least one broken-circuit witness. -/
def IsNBCBad (M : Matroid α) (A : Finset α) : Prop :=
  Finset.Nonempty (nbcCandidates M A)

lemma nbcCandidate_mem_ground {M : Matroid α} {A : Finset α} {e : α}
    (h : IsNBCandidate M A e) : e ∈ matroidGround M := by
  rcases h with ⟨C, hC, heC, _, _⟩
  apply (mem_matroidGround M e).2
  exact hC.subset_ground (by simpa using heC)

lemma mem_nbcCandidates {M : Matroid α} {A : Finset α} {e : α} :
    e ∈ nbcCandidates M A ↔ e ∈ matroidGround M ∧ IsNBCandidate M A e := by
  classical
  simp [nbcCandidates]

/-- The least circuit-completing element, chosen to define the cancellation pairing. -/
noncomputable def leastNBCandidate (M : Matroid α) (A : Finset α)
    (h : IsNBCBad M A) : α :=
  (nbcCandidates M A).min' h

lemma leastNBCandidate_mem {M : Matroid α} {A : Finset α}
    (h : IsNBCBad M A) :
    leastNBCandidate M A h ∈ nbcCandidates M A := by
  exact Finset.min'_mem _ _

lemma leastNBCandidate_isCandidate {M : Matroid α} {A : Finset α}
    (h : IsNBCBad M A) :
    IsNBCandidate M A (leastNBCandidate M A h) := by
  exact (mem_nbcCandidates.mp (leastNBCandidate_mem h)).2

lemma leastNBCandidate_le {M : Matroid α} {A : Finset α}
    (h : IsNBCBad M A) {e : α} (he : IsNBCandidate M A e) :
    leastNBCandidate M A h ≤ e := by
  apply Finset.min'_le
  exact (mem_nbcCandidates.mpr ⟨nbcCandidate_mem_ground he, he⟩)

/-- Remove an element if present and insert it otherwise. -/
def toggleEdge (A : Finset α) (e : α) : Finset α :=
  if e ∈ A then A.erase e else insert e A

omit [Fintype α] [LinearOrder α] in
lemma toggleEdge_toggleEdge (A : Finset α) (e : α) :
    toggleEdge (toggleEdge A e) e = A := by
  by_cases h : e ∈ A <;> simp [toggleEdge, h]

omit [Fintype α] [LinearOrder α] in
lemma toggleEdge_ne (A : Finset α) (e : α) : toggleEdge A e ≠ A := by
  by_cases h : e ∈ A <;> simp [toggleEdge, h]

omit [Fintype α] [LinearOrder α] in
lemma card_toggleEdge (A : Finset α) (e : α) :
    (toggleEdge A e).card = if e ∈ A then A.card - 1 else A.card + 1 := by
  by_cases h : e ∈ A <;> simp [toggleEdge, h]

omit [Fintype α] in
lemma candidate_toggleEdge {M : Matroid α} {A : Finset α} {e : α}
    (h : IsNBCandidate M A e) :
    IsNBCandidate M (toggleEdge A e) e := by
  rcases h with ⟨C, hC, heC, hmax, hsub⟩
  refine ⟨C, hC, heC, hmax, ?_⟩
  intro x hx
  have hxA : x ∈ A := hsub hx
  have hxe : x ≠ e := by
    intro hxe
    subst x
    exact (Finset.ne_of_mem_erase hx) rfl
  by_cases heA : e ∈ A
  · simp [toggleEdge, heA, hxe, hxA]
  · simp [toggleEdge, heA, hxA]

omit [Fintype α] in
lemma candidate_smaller_toggle_iff {M : Matroid α} {A : Finset α}
    {e f : α} (hfe : f < e) :
    IsNBCandidate M (toggleEdge A e) f ↔ IsNBCandidate M A f := by
  constructor
  · intro h
    rcases h with ⟨C, hC, hfC, hmax, hsub⟩
    refine ⟨C, hC, hfC, hmax, ?_⟩
    intro x hx
    have hxe : x ≠ e := by
      intro hxe
      subst x
      have heC : e ∈ C := Finset.mem_of_mem_erase hx
      have hle : e ≤ f := hmax e heC
      exact (not_le_of_gt hfe) hle
    have hxt : x ∈ toggleEdge A e := hsub hx
    by_cases heA : e ∈ A
    · simpa [toggleEdge, heA, hxe] using hxt
    · rcases (by simpa [toggleEdge, heA] using hxt) with hxeq | hxa
      · exact (False.elim (hxe hxeq))
      · exact hxa
  · intro h
    rcases h with ⟨C, hC, hfC, hmax, hsub⟩
    refine ⟨C, hC, hfC, hmax, ?_⟩
    intro x hx
    have hxA : x ∈ A := hsub hx
    have hxe : x ≠ e := by
      intro hxe
      subst x
      have heC : e ∈ C := Finset.mem_of_mem_erase hx
      have hle : e ≤ f := hmax e heC
      exact (not_le_of_gt hfe) hle
    by_cases heA : e ∈ A
    · simp [toggleEdge, heA, hxe, hxA]
    · simp [toggleEdge, heA, hxA]

lemma leastNBCandidate_toggle_eq {M : Matroid α} {A : Finset α}
    (h : IsNBCBad M A) :
    leastNBCandidate M (toggleEdge A (leastNBCandidate M A h))
        (by
          have hc := leastNBCandidate_isCandidate h
          exact ⟨leastNBCandidate M A h,
            mem_nbcCandidates.mpr
              ⟨nbcCandidate_mem_ground (candidate_toggleEdge hc),
                candidate_toggleEdge hc⟩⟩) =
      leastNBCandidate M A h := by
  let e := leastNBCandidate M A h
  let h' : IsNBCBad M (toggleEdge A e) := by
    have hc : IsNBCandidate M A e := leastNBCandidate_isCandidate h
    exact ⟨e, mem_nbcCandidates.mpr
      ⟨nbcCandidate_mem_ground (candidate_toggleEdge hc), candidate_toggleEdge hc⟩⟩
  have he' : IsNBCandidate M (toggleEdge A e)
      (leastNBCandidate M (toggleEdge A e) h') :=
    leastNBCandidate_isCandidate h'
  have hle₁ : leastNBCandidate M (toggleEdge A e) h' ≤ e := by
    apply Finset.min'_le
    have hec : IsNBCandidate M (toggleEdge A e) e :=
      candidate_toggleEdge (leastNBCandidate_isCandidate h)
    exact mem_nbcCandidates.mpr ⟨nbcCandidate_mem_ground hec, hec⟩
  have hle₂ : e ≤ leastNBCandidate M (toggleEdge A e) h' := by
    by_contra hn
    have hlt : leastNBCandidate M (toggleEdge A e) h' < e :=
      lt_of_not_ge hn
    have he_back : IsNBCandidate M A
        (leastNBCandidate M (toggleEdge A e) h') :=
      (candidate_smaller_toggle_iff hlt).mp he'
    exact (not_lt_of_ge (leastNBCandidate_le h he_back)) hlt
  have heq : leastNBCandidate M (toggleEdge A e) h' = e :=
    le_antisymm hle₁ hle₂
  simp [e, heq]

/-- The alternating sign determined by a natural-number cardinality. -/
def matroidParitySign : Nat -> Int
  | 0 => 1
  | n + 1 => -matroidParitySign n

lemma matroidParitySign_succ (n : Nat) :
    matroidParitySign (n + 1) = -matroidParitySign n := by
  rfl

omit [Fintype α] [LinearOrder α] in
lemma toggleEdge_sign {A : Finset α} {e : α} :
    matroidParitySign (toggleEdge A e).card =
      -matroidParitySign A.card := by
  by_cases h : e ∈ A
  · rw [show toggleEdge A e = A.erase e by simp [toggleEdge, h]]
    rw [← Finset.card_erase_add_one h, matroidParitySign_succ]
    simp
  · have hcard : (toggleEdge A e).card = A.card + 1 := by
      simp [toggleEdge, h]
    rw [hcard, matroidParitySign_succ]

/-- Enumerate the spanning subsets of the matroid ground set. -/
noncomputable def spanningSubsets (M : Matroid α) : Finset (Finset α) := by
  classical
  exact (matroidGround M).powerset.filter (fun A => M.Spanning (A : Set α))

/-- Enumerate spanning subsets with a broken-circuit witness. -/
noncomputable def badSpanningSubsets (M : Matroid α) : Finset (Finset α) := by
  classical
  exact (spanningSubsets M).filter (IsNBCBad M)

/-- Enumerate the bases of the matroid. -/
noncomputable def baseSubsets (M : Matroid α) : Finset (Finset α) := by
  classical
  exact (matroidGround M).powerset.filter (fun A => M.IsBase (A : Set α))

omit [DecidableEq α] [LinearOrder α] in
lemma mem_spanningSubsets {M : Matroid α} {A : Finset α}
    (hA : A ∈ spanningSubsets M) : M.Spanning (A : Set α) := by
  classical
  exact (Finset.mem_filter.mp hA).2

lemma mem_badSpanningSubsets {M : Matroid α} {A : Finset α}
    (hA : A ∈ badSpanningSubsets M) :
    M.Spanning (A : Set α) ∧ IsNBCBad M A := by
  classical
  exact ⟨mem_spanningSubsets (Finset.mem_filter.mp hA).1,
    (Finset.mem_filter.mp hA).2⟩

omit [Fintype α] in
lemma spanning_toggleEdge {M : Matroid α} {A : Finset α} {e : α}
    (hA : M.Spanning (A : Set α)) (he : IsNBCandidate M A e) :
    M.Spanning (toggleEdge A e : Set α) := by
  classical
  rcases he with ⟨C, hC, heC, hmax, hsub⟩
  by_cases heA : e ∈ A
  · rw [show toggleEdge A e = A.erase e by simp [toggleEdge, heA]]
    have hEraseGround : (A.erase e : Set α) ⊆ M.E := by
      intro x hx
      exact hA.subset_ground (Finset.mem_of_mem_erase hx)
    have hCErase : (C.erase e : Set α) ⊆ (A.erase e : Set α) := by
      intro x hx
      have hxA : x ∈ A := hsub hx
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx, hxA⟩
    have heClosure : e ∈ M.closure (A.erase e : Set α) := by
      apply (M.closure_subset_closure hCErase)
      simpa only [Finset.coe_erase] using
        hC.mem_closure_sdiff_singleton_of_mem (by simpa using heC)
    have hAClosure : (A : Set α) ⊆ M.closure (A.erase e : Set α) := by
      intro x hx
      by_cases hxe : x = e
      · simpa [hxe] using heClosure
      · apply (M.subset_closure (A.erase e : Set α) hEraseGround)
        exact Finset.mem_erase.mpr ⟨hxe, hx⟩
    apply (Matroid.spanning_iff_ground_subset_closure hEraseGround).2
    rw [← hA.closure_eq]
    exact M.closure_subset_closure_of_subset_closure hAClosure
  · rw [show toggleEdge A e = insert e A by simp [toggleEdge, heA]]
    have hInsertGround : (insert e A : Set α) ⊆ M.E := by
      intro x hx
      rcases (by simpa using hx) with rfl | hxA
      · exact hC.subset_ground (by simpa using heC)
      · exact hA.subset_ground hxA
    have hInsertGround' : (↑(insert e A) : Set α) ⊆ M.E := by
      simpa only [Finset.coe_insert] using hInsertGround
    exact hA.superset (hT := hInsertGround') (by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert]
      exact Or.inr hx)

lemma mem_badSpanningSubsets_iff {M : Matroid α} {A : Finset α} :
    A ∈ badSpanningSubsets M ↔
      A ∈ spanningSubsets M ∧ IsNBCBad M A := by
  classical
  simp [badSpanningSubsets]

lemma toggle_mem_badSpanningSubsets {M : Matroid α} {A : Finset α}
    (hA : A ∈ badSpanningSubsets M) :
    toggleEdge A (leastNBCandidate M A (mem_badSpanningSubsets hA).2) ∈
      badSpanningSubsets M := by
  classical
  let e := leastNBCandidate M A (mem_badSpanningSubsets hA).2
  have hc : IsNBCandidate M A e :=
    leastNBCandidate_isCandidate (mem_badSpanningSubsets hA).2
  have hspan : M.Spanning (toggleEdge A e : Set α) :=
    spanning_toggleEdge (mem_badSpanningSubsets hA).1 hc
  have hground : toggleEdge A e ∈ (matroidGround M).powerset := by
    apply Finset.mem_powerset.mpr
    intro x hx
    apply (mem_matroidGround M x).2
    exact hspan.subset_ground hx
  apply mem_badSpanningSubsets_iff.mpr
  refine ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hground, hspan⟩
  · have hbad : IsNBCBad M (toggleEdge A e) := by
      exact ⟨e, mem_nbcCandidates.mpr
        ⟨nbcCandidate_mem_ground (candidate_toggleEdge hc), candidate_toggleEdge hc⟩⟩
    exact hbad

lemma toggle_bad_involutive {M : Matroid α} {A : Finset α}
    (hA : A ∈ badSpanningSubsets M) :
    toggleEdge
        (toggleEdge A (leastNBCandidate M A (mem_badSpanningSubsets hA).2))
        (leastNBCandidate M
          (toggleEdge A (leastNBCandidate M A (mem_badSpanningSubsets hA).2))
          (by
            have hc := leastNBCandidate_isCandidate (mem_badSpanningSubsets hA).2
            exact ⟨_, mem_nbcCandidates.mpr
              ⟨nbcCandidate_mem_ground (candidate_toggleEdge hc),
                candidate_toggleEdge hc⟩⟩)) = A := by
  classical
  let e := leastNBCandidate M A (mem_badSpanningSubsets hA).2
  have hbad' : IsNBCBad M (toggleEdge A e) := by
    exact (mem_badSpanningSubsets_iff.mp
      (toggle_mem_badSpanningSubsets hA)).2
  have heq : leastNBCandidate M (toggleEdge A e) hbad' = e := by
    exact leastNBCandidate_toggle_eq (mem_badSpanningSubsets hA).2
  rw [show leastNBCandidate M (toggleEdge A e)
      (by
        have hc := leastNBCandidate_isCandidate (mem_badSpanningSubsets hA).2
        exact ⟨e, mem_nbcCandidates.mpr
          ⟨nbcCandidate_mem_ground (candidate_toggleEdge hc),
            candidate_toggleEdge hc⟩⟩) = e by
      apply leastNBCandidate_toggle_eq (mem_badSpanningSubsets hA).2]
  exact toggleEdge_toggleEdge A e

lemma spanning_not_nbcBad_isIndependent {M : Matroid α} {A : Finset α}
    (hA : A ∈ spanningSubsets M) (hbad : ¬IsNBCBad M A) :
    M.Indep (A : Set α) := by
  classical
  by_contra hI
  have hground : (A : Set α) ⊆ M.E :=
    (mem_spanningSubsets hA).subset_ground
  have hdep : M.Dep (A : Set α) := ⟨hI, hground⟩
  obtain ⟨C, hCA, hC⟩ :=
    (Matroid.dep_iff_superset_isCircuit hground).mp hdep
  have hC_nonempty : C.Nonempty := by
    rcases hC.nonempty with ⟨e, he⟩
    exact ⟨e, by simpa using he⟩
  let C' : Finset α := hC.finite.toFinset
  have hC' : M.IsCircuit (C' : Set α) := by
    simpa [C', hC.finite.coe_toFinset] using hC
  have hC'_nonempty : C'.Nonempty := by
    rw [← Finset.coe_nonempty]
    simpa [C', hC.finite.coe_toFinset] using hC_nonempty
  let e := C'.max' hC'_nonempty
  have heC : e ∈ C' := C'.max'_mem hC'_nonempty
  have hmax : ∀ f ∈ C', f ≤ e := fun f hf => C'.le_max' f hf
  have hsub : ((C'.erase e : Finset α) : Set α) ⊆ (A : Set α) := by
    intro x hx
    apply hCA
    apply (hC.finite.mem_toFinset).mp
    exact Finset.mem_of_mem_erase hx
  have hc : IsNBCandidate M A e := ⟨C', hC', heC, hmax, hsub⟩
  exact hbad ⟨e, mem_nbcCandidates.mpr ⟨nbcCandidate_mem_ground hc, hc⟩⟩

/-- Enumerate spanning sets with no broken circuit, which are the surviving bases. -/
noncomputable def nbcBaseSubsets (M : Matroid α) : Finset (Finset α) := by
  classical
  exact (spanningSubsets M).filter (fun A => ¬IsNBCBad M A)

lemma mem_nbcBaseSubsets {M : Matroid α} {A : Finset α}
    (hA : A ∈ nbcBaseSubsets M) :
    A ∈ spanningSubsets M ∧ ¬IsNBCBad M A := by
  classical
  exact Finset.mem_filter.mp hA

lemma nbcBase_isBase {M : Matroid α} {A : Finset α}
    (hA : A ∈ nbcBaseSubsets M) : M.IsBase (A : Set α) := by
  have h := mem_nbcBaseSubsets hA
  exact (spanning_not_nbcBad_isIndependent h.1 h.2).isBase_of_spanning
    (mem_spanningSubsets h.1)

/-- The sum of cardinality-parity signs over all spanning subsets. -/
noncomputable def signedSpanningSum (M : Matroid α) : Int :=
  ∑ A ∈ spanningSubsets M, matroidParitySign A.card

/-- The sum of cardinality-parity signs over the surviving no-broken-circuit sets. -/
noncomputable def signedNBCSum (M : Matroid α) : Int :=
  ∑ A ∈ nbcBaseSubsets M, matroidParitySign A.card

lemma badSpanningSum_zero (M : Matroid α) :
    (∑ A ∈ badSpanningSubsets M, matroidParitySign A.card) = 0 := by
  classical
  let g : ∀ A, A ∈ badSpanningSubsets M → Finset α := fun A hA =>
    toggleEdge A (leastNBCandidate M A (mem_badSpanningSubsets hA).2)
  apply Finset.sum_involution g
  · intro A hA
    change matroidParitySign A.card +
      matroidParitySign (g A hA).card = 0
    rw [show g A hA =
        toggleEdge A (leastNBCandidate M A (mem_badSpanningSubsets hA).2) by rfl]
    rw [toggleEdge_sign]
    simp
  · intro A hA _
    change toggleEdge A
      (leastNBCandidate M A (mem_badSpanningSubsets hA).2) ≠ A
    exact toggleEdge_ne A _
  · intro A hA
    simpa [g] using toggle_bad_involutive hA
  · intro A hA
    simpa [g] using toggle_mem_badSpanningSubsets hA

theorem signed_spanning_eq_signed_nbc (M : Matroid α) :
    signedSpanningSum M = signedNBCSum M := by
  classical
  unfold signedSpanningSum signedNBCSum
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (spanningSubsets M) (IsNBCBad M)
    (fun A => matroidParitySign A.card)
  rw [← hsplit]
  have hbad :
      (∑ A ∈ spanningSubsets M with IsNBCBad M A,
        matroidParitySign A.card) = 0 := by
    simpa [badSpanningSubsets] using badSpanningSum_zero M
  rw [hbad]
  simp [nbcBaseSubsets]

end HsVirial
