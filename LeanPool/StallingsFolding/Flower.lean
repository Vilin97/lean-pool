/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import LeanPool.StallingsFolding.Folding
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Sigma.Order
public import Mathlib.Data.Sum.Order

/-!
# The flower graph of a finite list of words

The flower graph has one common basepoint and one loop spelling each input
word. Its vertices are indexed by generator and letter position, so the
construction is finite and the input words remain visible in the definition.
-/

@[expose] public section

namespace Stallings

/-- The maximum length of a word in a finite input list. -/
def maxWordLength : List Word → Nat
  | [] => 0
  | w :: ws => max w.length (maxWordLength ws)

theorem length_le_maxWordLength_of_mem {S : List Word} {w : Word} (h : w ∈ S) :
    w.length ≤ maxWordLength S := by
  induction S with
  | nil => simp at h
  | cons u S ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)

/-- A finite vertex type for the flower of `S`. `none` is the common basepoint;
`some ⟨i,k⟩` is the vertex after `k + 1` letters of the `i`th generator.
Only internal positions are retained; empty and singleton words add no vertices. -/
abbrev FlowerVertex (S : List Word) := Option (Σ i : Fin S.length, Fin ((S.get i).length - 1))

/-- Encode flower vertices in a finite lexicographic order. -/
def flowerVertexOrderCode {S : List Word} :
    FlowerVertex S → Unit ⊕ₗ (Σₗ i : Fin S.length, Fin ((S.get i).length - 1))
  | none => toLex (Sum.inl ())
  | some p => toLex (Sum.inr (toLex p))

theorem flowerVertexOrderCode_injective {S : List Word} :
    Function.Injective (@flowerVertexOrderCode S) := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some b =>
          have hsum := toLex_inj.mp h
          cases hsum
  | some a =>
      cases y with
      | none =>
          have hsum := toLex_inj.mp h
          cases hsum
      | some b =>
          have hsum := toLex_inj.mp h
          have hp : toLex a = toLex b := Sum.inr.inj hsum
          have hab : a = b := toLex_inj.mp hp
          exact congrArg Option.some hab

instance flowerVertexLinearOrder (S : List Word) : LinearOrder (FlowerVertex S) :=
  LinearOrder.lift' flowerVertexOrderCode flowerVertexOrderCode_injective

/-- The vertex at position `k` while reading generator `i`, with both endpoints
of the generator loop identified with the common basepoint. -/
def flowerPos (S : List Word) (i : Fin S.length) (k : Nat)
    (hk : k ≤ (S.get i).length) : FlowerVertex S :=
  if hk0 : k = 0 then none
  else if hkend : k = (S.get i).length then none
  else
    some ⟨i, ⟨k - 1, by omega⟩⟩

/-- The source vertex of the edge in position `j` of a generator. -/
def flowerSource (S : List Word) (i : Fin S.length) (j : Fin (S.get i).length) :
    FlowerVertex S :=
  flowerPos S i j.val (Nat.le_of_lt j.isLt)

/-- The target vertex of the edge in position `j` of a generator. -/
def flowerTarget (S : List Word) (i : Fin S.length) (j : Fin (S.get i).length) :
    FlowerVertex S :=
  flowerPos S i (j.val + 1) (Nat.succ_le_of_lt j.isLt)

/-- The signed letter at position `j` of input generator `i`. -/
def flowerLabel (S : List Word) (i : Fin S.length) (j : Fin (S.get i).length) : Letter :=
  (S.get i).get j

/-- A directed edge, allowing either the forward letter in an input word or its
inverse orientation. -/
def flowerEdge (S : List Word) (v : FlowerVertex S) (x : Letter)
    (w : FlowerVertex S) : Prop :=
  ∃ i : Fin S.length, ∃ j : Fin (S.get i).length,
    (v = flowerSource S i j ∧ w = flowerTarget S i j ∧ x = flowerLabel S i j) ∨
    (v = flowerTarget S i j ∧ w = flowerSource S i j ∧
      x = letterInv (flowerLabel S i j))

instance flowerEdgeDecidable (S : List Word) (v : FlowerVertex S) (x : Letter) :
    DecidablePred (flowerEdge S v x) := by
  intro w
  unfold flowerEdge
  infer_instance

theorem flowerEdge_inv {S : List Word} {v w : FlowerVertex S} {x : Letter}
    (h : flowerEdge S v x w) : flowerEdge S w (letterInv x) v := by
  rcases h with ⟨i, j, hforward | hbackward⟩
  · rcases hforward with ⟨hv, hw, hx⟩
    refine ⟨i, j, Or.inr ⟨hw, hv, ?_⟩⟩
    simp [hx]
  · rcases hbackward with ⟨hv, hw, hx⟩
    refine ⟨i, j, Or.inl ⟨hw, hv, ?_⟩⟩
    rw [hx]
    simp

theorem flowerEdge_inv_iff {S : List Word} (v w : FlowerVertex S) (x : Letter) :
    flowerEdge S v x w ↔ flowerEdge S w (letterInv x) v := by
  constructor
  · exact flowerEdge_inv
  · intro h
    have h' := flowerEdge_inv h
    simpa using h'

/-- The initial bouquet of loops spelling the words in `S`. -/
def flowerGraph (S : List Word) : InverseMultigraph (FlowerVertex S) where
  edges v x := (Finset.univ : Finset (FlowerVertex S)).filter (flowerEdge S v x)
  inverse_edges := by
    intro v x w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact flowerEdge_inv_iff v w x

/-- The subgroup generated by the words in the input list. -/
def generatorSubgroup (S : List Word) : Subgroup Free :=
  Subgroup.closure (Set.range fun i : Fin S.length => wordEval (S.get i))

/-- The word prefix reaching an internal flower vertex, with `1` at the basepoint. -/
def flowerPotential (S : List Word) : FlowerVertex S → Free
  | none => 1
  | some ⟨i, k⟩ => wordEval ((S.get i).take (k.val + 1))

private theorem flowerPos_internal (S : List Word) (i : Fin S.length) {k : Nat}
    (hk0 : 0 < k) (hk : k < (S.get i).length) :
    flowerPos S i k (Nat.le_of_lt hk) = some ⟨i, ⟨k - 1, by omega⟩⟩ := by
  unfold flowerPos
  rw [dite_eq_right (by omega : ¬ k = 0), dite_eq_right (by omega : ¬ k = (S.get i).length)]

private theorem flowerPotential_pos (S : List Word) (i : Fin S.length) {k : Nat}
    (hk : k < (S.get i).length) :
    flowerPotential S (flowerPos S i k (Nat.le_of_lt hk)) =
      wordEval ((S.get i).take k) := by
  by_cases hk0 : k = 0
  · subst k
    simp [flowerPos, flowerPotential, wordEval_nil]
  · have hpos := flowerPos_internal S i (Nat.pos_of_ne_zero hk0) hk
    rw [hpos]
    change wordEval ((S.get i).take (k - 1 + 1)) = _
    rw [Nat.sub_add_cancel (by omega)]

private theorem wordEval_take_succ (w : Word) (k : Nat) (hk : k < w.length) :
    wordEval (w.take (k + 1)) = wordEval (w.take k) * letterEval (w.get ⟨k, hk⟩) := by
  rw [← List.take_concat_get' w k hk, wordEval_append]
  simp

/-- The forward edge from a generator position is consistent with the word
potential, modulo the subgroup generated by the input loops. -/
private theorem flowerForwardPotential (S : List Word) (i : Fin S.length)
    (j : Fin (S.get i).length) :
    CosetEquivalent (generatorSubgroup S)
      (flowerPotential S (flowerTarget S i j))
      (flowerPotential S (flowerSource S i j) * letterEval (flowerLabel S i j)) := by
  let w := S.get i
  let k := j.val
  have hk : k < w.length := j.isLt
  have hsource : flowerPotential S (flowerSource S i j) = wordEval (w.take k) := by
    simpa [flowerSource, w, k] using flowerPotential_pos S i hk
  have hstep : wordEval (w.take (k + 1)) =
      wordEval (w.take k) * letterEval (flowerLabel S i j) := by
    simpa [w, k, flowerLabel] using wordEval_take_succ w k hk
  have hkNext : k + 1 ≤ w.length := Nat.succ_le_of_lt hk
  by_cases hinternal : k + 1 < w.length
  · have htarget : flowerPotential S (flowerTarget S i j) = wordEval (w.take (k + 1)) := by
      simpa [flowerTarget, w, k] using flowerPotential_pos S i hinternal
    have hval : flowerPotential S (flowerTarget S i j) =
        flowerPotential S (flowerSource S i j) * letterEval (flowerLabel S i j) := by
      rw [htarget, hsource, ← hstep]
    rw [hval]
    exact CosetEquivalent.refl _ _
  · have hterminal : k + 1 = w.length := by omega
    have htarget : flowerPotential S (flowerTarget S i j) = 1 := by
      change flowerPotential S (flowerPos S i (k + 1) hkNext) = 1
      unfold flowerPos
      rw [dite_eq_right (by omega : ¬ k + 1 = 0), dite_eq_left hterminal]
      simp [flowerPotential]
    have htake : w.take (k + 1) = w := by
      apply List.take_of_length_le
      omega
    have hgen : wordEval w ∈ generatorSubgroup S :=
      Subgroup.subset_closure ⟨i, rfl⟩
    have hcoset : CosetEquivalent (generatorSubgroup S) 1 (wordEval w) := by
      change (wordEval w)⁻¹ ∈ generatorSubgroup S
      exact (generatorSubgroup S).inv_mem hgen
    rw [htarget, hsource, ← hstep, htake]
    simpa using hcoset

/-- The input flower has a coset potential for the subgroup generated by its
loop labels. -/
theorem flower_hasCosetPotential (S : List Word) :
    HasCosetPotential (flowerGraph S) (generatorSubgroup S) (flowerPotential S) := by
  intro v x w hedge
  change w ∈ (Finset.univ.filter (flowerEdge S v x)) at hedge
  have hedg := (Finset.mem_filter.mp hedge).2
  rcases hedg with ⟨i, j, hforward | hbackward⟩
  · rcases hforward with ⟨rfl, rfl, rfl⟩
    exact flowerForwardPotential S i j
  · rcases hbackward with ⟨rfl, rfl, rfl⟩
    have hf := flowerForwardPotential S i j
    have hr := CosetEquivalent.right_mul hf (letterEval (letterInv (flowerLabel S i j)))
    simpa [letterEval_inv, mul_assoc] using CosetEquivalent.symm hr

private theorem flowerPos_zero (S : List Word) (i : Fin S.length) :
    flowerPos S i 0 (Nat.zero_le _) = none := by
  simp [flowerPos]

private theorem flowerPos_end (S : List Word) (i : Fin S.length) :
    flowerPos S i (S.get i).length (Nat.le_refl _) = none := by
  simp [flowerPos]

/-- The position-indexed path through one generator loop. -/
private theorem flowerWalkAux (S : List Word) (i : Fin S.length) :
    ∀ (k : Nat) (suffix : Word) (hk : k ≤ (S.get i).length),
      (S.get i).drop k = suffix →
      (flowerGraph S).Walk (flowerPos S i k hk) suffix none := by
  intro k suffix hk hdrop
  induction suffix generalizing k with
  | nil =>
      have hlen : (S.get i).length ≤ k := by
        by_contra hnot
        have hlt : k < (S.get i).length := Nat.lt_of_not_ge hnot
        have hcons := List.drop_eq_getElem_cons (l := S.get i) hlt
        rw [hdrop] at hcons
        cases hcons
      have hkEq : k = (S.get i).length := le_antisymm hk hlen
      subst k
      simpa [flowerPos] using (InverseMultigraph.Walk.nil (G := flowerGraph S) none)
  | cons x xs ih =>
      have hlt : k < (S.get i).length := by
        by_contra hnot
        have hlen : (S.get i).length ≤ k := Nat.le_of_not_gt hnot
        rw [List.drop_eq_nil_of_le hlen] at hdrop
        contradiction
      have hdropCons : (S.get i).drop k =
          (S.get i).get ⟨k, hlt⟩ :: (S.get i).drop (k + 1) :=
        List.drop_eq_getElem_cons hlt
      have hparts := hdrop.symm.trans hdropCons
      rcases List.cons.inj hparts with ⟨rfl, htail⟩
      have hkNext : k + 1 ≤ (S.get i).length := Nat.succ_le_of_lt hlt
      let j : Fin (S.get i).length := ⟨k, hlt⟩
      have hsource : flowerSource S i j = flowerPos S i k hk := by
        simp [flowerSource, j]
      have htarget : flowerTarget S i j = flowerPos S i (k + 1) hkNext := by
        simp [flowerTarget, j]
      have hedge : flowerTarget S i j ∈ (flowerGraph S).edges
          (flowerSource S i j) (flowerLabel S i j) := by
        change flowerTarget S i j ∈
          (Finset.univ.filter (flowerEdge S (flowerSource S i j) (flowerLabel S i j)))
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact ⟨i, j, Or.inl ⟨rfl, rfl, rfl⟩⟩
      rw [hsource, htarget] at hedge
      have htailWalk := ih (k + 1) hkNext htail.symm
      exact InverseMultigraph.Walk.cons (G := flowerGraph S) hedge htailWalk

/-- Each input word labels a closed path in the flower graph. -/
theorem flowerWalk (S : List Word) (i : Fin S.length) :
    (flowerGraph S).Walk none (S.get i) none := by
  have h := flowerWalkAux S i 0 (S.get i) (Nat.zero_le _) List.drop_zero
  simpa [flowerPos_zero] using h

/-- The loop subgroup of the initial flower is exactly the subgroup generated
by the input words. -/
theorem flowerGraph_loopSubgroup_eq_generatorSubgroup (S : List Word) :
    (flowerGraph S).loopSubgroup none = generatorSubgroup S := by
  apply le_antisymm
  · change Subgroup.closure
      {g : Free | ∃ w : Word, wordEval w = g ∧ (flowerGraph S).Walk none w none} ≤
      generatorSubgroup S
    apply (Subgroup.closure_le (generatorSubgroup S)).2
    intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    rw [← hw]
    have hpotential := InverseMultigraph.walk_cosetPotential (flowerGraph S)
      (generatorSubgroup S) (flowerPotential S) (flower_hasCosetPotential S) hwalk
    have hcoset : CosetEquivalent (generatorSubgroup S) 1 (wordEval w) := by
      simpa [flowerPotential] using hpotential
    have hinv : (wordEval w)⁻¹ ∈ generatorSubgroup S := by
      simpa [CosetEquivalent] using hcoset
    simpa using (generatorSubgroup S).inv_mem hinv
  · apply (Subgroup.closure_le ((flowerGraph S).loopSubgroup none)).2
    intro g hg
    rcases hg with ⟨i, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨S.get i, rfl, flowerWalk S i⟩

/-- The folded automaton constructed from a finite generator list. -/
def foldWords (S : List Word) : InverseAutomaton (FlowerVertex S) :=
  foldAutomaton (flowerGraph S) none

/-- The folded automaton's based-loop subgroup is exactly the subgroup
generated by the input words. -/
theorem foldWords_loopSubgroup_eq_generatorSubgroup (S : List Word) :
    (foldWords S).loopSubgroup = generatorSubgroup S := by
  calc
    (foldWords S).loopSubgroup = (flowerGraph S).loopSubgroup none := by
      have hpotential : HasCosetPotential (flowerGraph S)
          ((flowerGraph S).loopSubgroup none) (flowerPotential S) := by
        intro v x w hedge
        have h := flower_hasCosetPotential S hedge
        rw [← flowerGraph_loopSubgroup_eq_generatorSubgroup S] at h
        exact h
      simpa [foldWords] using foldAutomaton_loopSubgroup_eq (flowerGraph S) none
        (flowerPotential S) hpotential (by rfl)
    _ = generatorSubgroup S := flowerGraph_loopSubgroup_eq_generatorSubgroup S

/-- Execute the Stallings membership test for the subgroup generated by `S`. -/
def foldedMembershipTest (S : List Word) (g : Free) : Bool :=
  (foldWords S).membershipTest g

/-- The executable folded-graph traversal accepts exactly the elements of the
subgroup generated by the supplied words. -/
theorem foldedMembershipTest_eq_true_iff (S : List Word) (g : Free) :
    foldedMembershipTest S g = true ↔ g ∈ generatorSubgroup S := by
  change (foldWords S).membershipTest g = true ↔ g ∈ generatorSubgroup S
  rw [InverseAutomaton.membershipTest_eq_true_iff,
    foldWords_loopSubgroup_eq_generatorSubgroup]

end Stallings
