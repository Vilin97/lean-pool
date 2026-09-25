/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralSwap
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.MixedTorsionChains
public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.OnceMarkedWedgeGenerality

/-!
# Balanced chains with mixed torsion orders

This file formalizes the second half of Corollary 6.16 (`thm:bngChain`).  A
chain is split at one of its separating vertices.  The factors on the left
obey the prefix-genus bounds of part (1), while the factors on the right obey
the corresponding suffix-genus bounds.  The right half is built from the
outside inward after swapping both marks of every factor.  Thus the suffix
bounds become the prefix bounds needed by Theorem 6.6.

The final graph is presented by its *central* vertex wedge.  This is a literal
iterated vertex gluing of the factors in their original order; choosing this
parenthesization avoids identifying the different nested `Sum` vertex types
of left- and right-associated `MarkedGraph.chain` constructions.
-/

@[expose] public section

namespace Bananas

open Utilities

/-! ## Reversing a chain factor -/

/-- Reverse the orientation of a twice-marked chain factor. -/
def KGeneralChainFactor.swapMarks (F : KGeneralChainFactor) :
    KGeneralChainFactor where
  marked := {
    graph := F.marked.graph
    left := F.marked.right
    right := F.marked.left
  }
  period := F.period
  connected := F.connected
  kGeneral := F.kGeneral.swap_marks F.marked.left F.marked.right

@[simp] theorem KGeneralChainFactor.swapMarks_graph
    (F : KGeneralChainFactor) :
    F.swapMarks.marked.graph = F.marked.graph := rfl

@[simp] theorem KGeneralChainFactor.swapMarks_left
    (F : KGeneralChainFactor) :
    F.swapMarks.marked.left = F.marked.right := rfl

@[simp] theorem KGeneralChainFactor.swapMarks_right
    (F : KGeneralChainFactor) :
    F.swapMarks.marked.right = F.marked.left := rfl

@[simp] theorem KGeneralChainFactor.swapMarks_period
    (F : KGeneralChainFactor) : F.swapMarks.period = F.period := rfl

/-! ## Genus budgets from the right -/

/-- The sum of the genera of a list of chain factors. -/
def chainFactorGenus (L : List KGeneralChainFactor) : ℤ :=
  (L.map fun F => genus F.marked.graph).sum

@[simp] theorem chainFactorGenus_nil : chainFactorGenus [] = 0 := by
  simp [chainFactorGenus]

@[simp] theorem chainFactorGenus_cons
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    chainFactorGenus (F :: rest) =
      genus F.marked.graph + chainFactorGenus rest := by
  simp [chainFactorGenus]

/-- The paper's suffix-genus inequalities.

For `Fᵢ, Fᵢ₊₁, ..., Fℓ`, the first conjunct says
`gᵢ + gᵢ₊₁ + ... + gℓ < kᵢ`; the recursive tail records the
same inequality at every later factor. -/
def ChainSuffixBudget : List KGeneralChainFactor → Prop
  | [] => True
  | F :: rest =>
      chainFactorGenus (F :: rest) < (F.period : ℤ) ∧
        ChainSuffixBudget rest

@[simp] theorem chainSuffixBudget_nil : ChainSuffixBudget [] := trivial

@[simp] theorem chainSuffixBudget_cons
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    ChainSuffixBudget (F :: rest) ↔
      chainFactorGenus (F :: rest) < (F.period : ℤ) ∧
        ChainSuffixBudget rest := Iff.rfl

/-- Indexed form of the recursive prefix budget. -/
theorem chainPrefixBudget_iff_indexed
    (g : ℤ) (L : List KGeneralChainFactor) :
    ChainPrefixBudget g L ↔
      ∀ (i : ℕ) (hi : i < L.length),
        g + chainFactorGenus (L.take (i + 1)) <
          ((L.get ⟨i, hi⟩).period : ℤ) := by
  induction L generalizing g with
  | nil => simp
  | cons F rest ih =>
      rw [chainPrefixBudget_cons]
      constructor
      · rintro ⟨hHead, hRest⟩ i hi
        cases i with
        | zero => simpa [chainFactorGenus] using hHead
        | succ i =>
            have hiRest : i < rest.length := by simpa using hi
            have h := (ih (g + genus F.marked.graph)).mp hRest i hiRest
            simpa [chainFactorGenus, add_assoc] using h
      · intro h
        constructor
        · simpa [chainFactorGenus] using h 0 (by simp)
        · apply (ih (g + genus F.marked.graph)).mpr
          intro i hi
          have h' := h (i + 1) (by simp; omega)
          simpa [chainFactorGenus, add_assoc] using h'

/-- Indexed form of the recursive suffix budget. -/
theorem chainSuffixBudget_iff_indexed (L : List KGeneralChainFactor) :
    ChainSuffixBudget L ↔
      ∀ (i : ℕ) (hi : i < L.length),
        chainFactorGenus (L.drop i) <
          ((L.get ⟨i, hi⟩).period : ℤ) := by
  induction L with
  | nil => simp
  | cons F rest ih =>
      rw [chainSuffixBudget_cons]
      constructor
      · rintro ⟨hHead, hRest⟩ i hi
        cases i with
        | zero => simpa using hHead
        | succ i =>
            have hiRest : i < rest.length := by simpa using hi
            simpa using (ih.mp hRest i hiRest)
      · intro h
        constructor
        · simpa using h 0 (by simp)
        · apply ih.mpr
          intro i hi
          simpa using h (i + 1) (by simp; omega)

/-- The literal minimum hypothesis in Corollary 6.16(2), indexed from zero. -/
def ChainMinBudget (L : List KGeneralChainFactor) : Prop :=
  ∀ (i : ℕ) (hi : i < L.length),
    min (chainFactorGenus (L.take (i + 1)))
        (chainFactorGenus (L.drop i)) <
      ((L.get ⟨i, hi⟩).period : ℤ)

/-- A cut lies at the crossing of the prefix- and suffix-genus functions.

Before the cut, each prefix is no larger than the corresponding suffix;
after the cut, each suffix is no larger than the corresponding prefix.  The
maximal index used in the paper's proof has exactly this property. -/
def ChainDominatesAtSplit
  (left right : List KGeneralChainFactor) : Prop :=
  (∀ (i : ℕ) (_hi : i < left.length),
      chainFactorGenus (left.take (i + 1)) ≤
        chainFactorGenus ((left ++ right).drop i)) ∧
    (∀ (i : ℕ) (_hi : i < right.length),
      chainFactorGenus (right.drop i) ≤
        chainFactorGenus
          ((left ++ right).take (left.length + i + 1)))

/-- The split form of the minimum condition in Corollary 6.16(2): on the
left side the minimum is the prefix genus, and on the right side it is the
suffix genus. -/
def ChainBalancedAtSplit
    (left right : List KGeneralChainFactor) : Prop :=
  ChainPrefixBudget 0 left ∧ ChainSuffixBudget right

/-- The paper's minimum hypothesis gives the two recursive budgets at any
crossing cut of the prefix- and suffix-genus functions. -/
theorem chainBalancedAtSplit_of_minBudget
    (left right : List KGeneralChainFactor)
    (hMin : ChainMinBudget (left ++ right))
    (hCross : ChainDominatesAtSplit left right) :
    ChainBalancedAtSplit left right := by
  constructor
  · apply (chainPrefixBudget_iff_indexed 0 left).mpr
    intro i hi
    have hiTotal : i < (left ++ right).length := by
      simp only [List.length_append]
      omega
    have h := hMin i hiTotal
    have hTake : (left ++ right).take (i + 1) = left.take (i + 1) :=
      List.take_append_of_le_length (by omega)
    have hGet : (left ++ right).get ⟨i, hiTotal⟩ = left.get ⟨i, hi⟩ := by
      change (left ++ right)[i] = left[i]
      exact List.getElem_append_left hi
    rw [hTake, hGet, min_eq_left (hCross.1 i hi)] at h
    simpa using h
  · apply (chainSuffixBudget_iff_indexed right).mpr
    intro i hi
    have hiTotal : left.length + i < (left ++ right).length := by
      simp only [List.length_append]
      omega
    have h := hMin (left.length + i) hiTotal
    have hDrop : (left ++ right).drop (left.length + i) = right.drop i := by
      rw [← List.drop_drop, List.drop_left]
    have hGet : (left ++ right).get ⟨left.length + i, hiTotal⟩ =
        right.get ⟨i, hi⟩ := by
      change (left ++ right)[left.length + i] = right[i]
      rw [List.getElem_append_right (by omega)]
      congr 1
      omega
    rw [hDrop, hGet, min_eq_right (hCross.2 i hi)] at h
    simpa using h

/-! ## The reversed right-hand chain -/

/-- Build a nonempty suffix from the outside inward.

For the original order `F :: next :: rest`, this is the chain whose factor
order is `reverse (F :: next :: rest)` and whose factor marks are all swapped.
Its right mark is therefore the original left mark of `F`, namely the vertex
at which this suffix is attached to the left half of the chain. -/
def reversedMarkedChain
    (F : KGeneralChainFactor) : List KGeneralChainFactor → MarkedGraph
  | [] => F.swapMarks.marked
  | next :: rest =>
      (reversedMarkedChain next rest).wedge F.swapMarks.marked

@[simp] theorem reversedMarkedChain_nil (F : KGeneralChainFactor) :
    reversedMarkedChain F [] = F.swapMarks.marked := rfl

@[simp] theorem reversedMarkedChain_cons
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    reversedMarkedChain F (next :: rest) =
      (reversedMarkedChain next rest).wedge F.swapMarks.marked := rfl

/-- The reversed chain has the sum of the original factor genera. -/
theorem genus_reversedMarkedChain
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    genus (reversedMarkedChain F rest).graph =
      chainFactorGenus (F :: rest) := by
  induction rest generalizing F with
  | nil => simp [reversedMarkedChain]
  | cons next rest ih =>
      rw [reversedMarkedChain_cons, MarkedGraph.genus_wedge, ih]
      simp [chainFactorGenus]
      ring

/-- Connectivity is preserved while the suffix is assembled from the right. -/
theorem graph_connected_reversedMarkedChain
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    _root_.graphConnected (reversedMarkedChain F rest).graph := by
  induction rest generalizing F with
  | nil => simpa [reversedMarkedChain] using F.connected
  | cons next rest ih =>
      rw [reversedMarkedChain_cons]
      exact graph_connected_vertexWedge
        (reversedMarkedChain next rest).graph F.marked.graph
        (reversedMarkedChain next rest).right F.marked.right
        (ih next) F.connected

/-- Every divisor on the reversed chain is submodular at its two outer marks. -/
theorem allSubmodular_reversedMarkedChain
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    AllSubmodular (mark (reversedMarkedChain F rest).graph
      (reversedMarkedChain F rest).left
      (reversedMarkedChain F rest).right) := by
  induction rest generalizing F with
  | nil =>
      simpa [reversedMarkedChain] using F.swapMarks.kGeneral.2.1
  | cons next rest ih =>
      rw [reversedMarkedChain_cons]
      exact allSubmodular_vertexWedge_opposite
        (reversedMarkedChain next rest).graph F.marked.graph
        (reversedMarkedChain next rest).right F.marked.right
        (graph_connected_reversedMarkedChain next rest) F.connected
        (reversedMarkedChain next rest).left F.marked.left
        (ih next) F.swapMarks.kGeneral.2.1

/-- The right-hand analogue of Corollary 6.16(1).

Under suffix-genus period bounds, the reversed chain is Brill--Noether
general as a once-marked graph at its central (right) mark. -/
theorem onceMarkedBrillNoetherGeneral_reversedMixedTorsionChain
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hBudget : ChainSuffixBudget (F :: rest)) :
    OnceMarkedBrillNoetherGeneral
      (reversedMarkedChain F rest).graph
      (reversedMarkedChain F rest).right := by
  induction rest generalizing F with
  | nil =>
      apply onceMarkedBrillNoetherGeneral_of_kGeneralTransmission
        F.marked.right F.marked.left F.connected F.swapMarks.kGeneral
      simpa [chainFactorGenus] using hBudget.1
  | cons next rest ih =>
      rw [reversedMarkedChain_cons]
      apply onceMarkedBrillNoetherGeneral_vertexWedge_of_kGeneralTransmission
        (reversedMarkedChain next rest).graph F.marked.graph
        (reversedMarkedChain next rest).left
        (reversedMarkedChain next rest).right
        F.marked.right F.marked.left
        (graph_connected_reversedMarkedChain next rest) F.connected
        (allSubmodular_reversedMarkedChain next rest)
        (ih next hBudget.2) F.swapMarks.kGeneral
      rw [genus_reversedMarkedChain]
      change chainFactorGenus (next :: rest) + genus F.marked.graph <
        (F.period : ℤ)
      simpa only [chainFactorGenus_cons, add_comm] using hBudget.1

/-! ## The central split and Corollary 6.16(2) -/

/-- Connectivity of a chain with a connected accumulated left factor. -/
private theorem graph_connected_markedChain
    (M : MarkedGraph) (hM : _root_.graphConnected M.graph)
    (rest : List KGeneralChainFactor) :
    _root_.graphConnected
      (M.chain (rest.map KGeneralChainFactor.marked)).graph := by
  induction rest generalizing M with
  | nil => simpa using hM
  | cons next rest ih =>
      rw [List.map_cons, MarkedGraph.chain_cons]
      exact ih (M.wedge next.marked)
        (graph_connected_vertexWedge
          M.graph next.marked.graph M.right next.marked.left
          hM next.connected)

/-- Connectivity of a left-associated nonempty factor chain. -/
theorem graph_connected_factorChain
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    _root_.graphConnected
      (F.marked.chain (rest.map KGeneralChainFactor.marked)).graph :=
  graph_connected_markedChain F.marked F.connected rest

/-- The graph obtained by gluing the two nonempty halves at their central
marks.  The right half is presented from the outside inward. -/
def balancedChainGraph
    (leftHead : KGeneralChainFactor)
    (leftTail : List KGeneralChainFactor)
    (rightHead : KGeneralChainFactor)
    (rightTail : List KGeneralChainFactor) : CFGraph :=
  let L := leftHead.marked.chain
    (leftTail.map KGeneralChainFactor.marked)
  let R := reversedMarkedChain rightHead rightTail
  vertexWedge L.graph R.graph L.right R.right

/-- **Paper Corollary 6.16(2), at a balancing split.**

If the factors to the left of a separating vertex satisfy their prefix-genus
bounds, while the factors to its right satisfy their suffix-genus bounds,
then the unmarked chain is Brill--Noether general.  Under the paper's global
`kᵢ > min(prefix genus, suffix genus)` hypothesis, its maximal balancing
index is exactly a split with these two properties. -/
theorem brillNoetherGeneral_mixedTorsionChain_of_balancedSplit
    (leftHead : KGeneralChainFactor)
    (leftTail : List KGeneralChainFactor)
    (rightHead : KGeneralChainFactor)
    (rightTail : List KGeneralChainFactor)
    (hBalanced : ChainBalancedAtSplit
      (leftHead :: leftTail) (rightHead :: rightTail)) :
    BrillNoetherGeneral
      (balancedChainGraph leftHead leftTail rightHead rightTail) := by
  let L := leftHead.marked.chain
    (leftTail.map KGeneralChainFactor.marked)
  let R := reversedMarkedChain rightHead rightTail
  apply onceMarkedBrillNoetherGeneral_vertexWedge
    L.graph R.graph
    (graph_connected_factorChain leftHead leftTail)
    (graph_connected_reversedMarkedChain rightHead rightTail)
    L.right R.right
  · exact onceMarkedBrillNoetherGeneral_mixedTorsionChain
      leftHead leftTail (by simpa using hBalanced.1.1)
      (by simpa using hBalanced.1.2)
  · exact onceMarkedBrillNoetherGeneral_reversedMixedTorsionChain
      rightHead rightTail hBalanced.2

/-- Corollary 6.16(2) in the paper's literal minimum-budget language, once
the crossing cut selected in its proof is supplied. -/
theorem brillNoetherGeneral_mixedTorsionChain_of_minBudget_at_crossing
    (leftHead : KGeneralChainFactor)
    (leftTail : List KGeneralChainFactor)
    (rightHead : KGeneralChainFactor)
    (rightTail : List KGeneralChainFactor)
    (hMin : ChainMinBudget
      ((leftHead :: leftTail) ++ (rightHead :: rightTail)))
    (hCross : ChainDominatesAtSplit
      (leftHead :: leftTail) (rightHead :: rightTail)) :
    BrillNoetherGeneral
      (balancedChainGraph leftHead leftTail rightHead rightTail) := by
  apply brillNoetherGeneral_mixedTorsionChain_of_balancedSplit
  exact chainBalancedAtSplit_of_minBudget _ _ hMin hCross

end Bananas
