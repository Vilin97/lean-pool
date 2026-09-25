/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.VertexWedgeAssociativity
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.MixedTorsionChainBalance
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainBalanceArithmetic
public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.ZeroGenusWedge
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralBNGeneral
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.ChainGluing

/-!
# The canonical mixed-torsion chain conclusion

This file transports the centered-wedge form of Corollary 6.16(2) to the
left-associated `MarkedGraph.chain` used in the statement of the paper.

The right half of a centered chain is assembled from the outside inward, so
the transport uses both commutativity and associativity of vertex wedges.
The generic commutativity isomorphism is recorded here; associativity is in
`VertexWedgeAssociativity`.
-/

@[expose] public section

namespace Bananas

open Utilities

universe u v

@[simp] theorem markedChain_append
    (M : Utilities.MarkedGraph) (L R : List Utilities.MarkedGraph) :
    M.chain (L ++ R) = (M.chain L).chain R := by
  induction L generalizing M with
  | nil => rfl
  | cons N L ih =>
      simpa only [List.cons_append, MarkedGraph.chain_cons] using ih (M.wedge N)

/-! ## Commuting a vertex wedge -/
/-- The wedge with its two factors exchanged, presented by the original
ordered pair of factors. -/
noncomputable def vertexWedgeCommPresentation
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    VertexWedgePresentation (vertexWedge H G y x) G H x y where
  leftMap := wedgeRightVertex H G y x
  rightMap := Sum.inl
  left_injective :=
    (VertexWedgePresentation.canonical H G y x).right_injective
  right_injective := Sum.inl_injective
  marked_eq := by simp
  only_overlap := by
    intro a b h
    have hEnds := (wedgeRightVertex_eq_left_iff H G y x a b).mp h
    exact hEnds
  vertex_cover := by
    rintro (b | a)
    · exact Or.inr ⟨b, rfl⟩
    · refine Or.inl ⟨a.1, ?_⟩
      exact wedgeRightVertex_unmarked H G y x a.1 a.2
  num_edges_left := by
    intro a b
    exact num_edges_vertexWedge_rightVertex H G y x a b
  num_edges_right := by
    intro a b
    exact num_edges_vertexWedge_left H G y x a b
  num_edges_cross := by
    intro a b hb
    by_cases ha : a = x
    · subst a
      simp
    · rw [if_neg ha]
      rw [wedgeRightVertex_unmarked H G y x a ha]
      rw [num_edges_vertexWedge_right_left]
      simp [hb]

/-- Vertex wedges are commutative up to graph isomorphism. -/
noncomputable def vertexWedgeComm
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    CFGraphIso (vertexWedge G H x y) (vertexWedge H G y x) :=
  (vertexWedgeCommPresentation G H x y).graphIso

@[simp] theorem vertexWedge_comm_apply_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (a : G.V) :
    (vertexWedgeComm G H x y).vertexEquiv (Sum.inl a) =
      wedgeRightVertex H G y x a := rfl

@[simp] theorem vertexWedge_comm_apply_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (b : H.V) :
    (vertexWedgeComm G H x y).vertexEquiv
        (wedgeRightVertex G H x y b) = Sum.inl b :=
  (vertexWedgeCommPresentation G H x y).graphIso_apply_wedgeRightVertex b

/-! ## Reassociating a marked chain -/

/-- Transport a right wedge attachment along an isomorphism that sends the
old attachment vertex to the specified new one.  Binding the target vertex
separately lets Lean eliminate the equality before the dependent wedge type is
formed. -/
noncomputable def vertexWedgeCongrRight
    {G : CFGraph.{u}} {H : CFGraph.{v}} {H' : CFGraph.{w}}
    (phi : CFGraphIso H H') (x : G.V) (y : H.V) (y' : H'.V)
    (hy : phi.vertexEquiv y = y') :
    CFGraphIso (vertexWedge G H x y) (vertexWedge G H' x y') := by
  subst y'
  exact (CFGraphIso.refl G).vertexWedgeCongr phi x y

@[simp] theorem vertexWedgeCongrRight_apply_left
    {G : CFGraph.{u}} {H : CFGraph.{v}} {H' : CFGraph.{w}}
    (phi : CFGraphIso H H') (x : G.V) (y : H.V) (y' : H'.V)
    (hy : phi.vertexEquiv y = y') (a : G.V) :
    (vertexWedgeCongrRight phi x y y' hy).vertexEquiv (Sum.inl a) = Sum.inl a := by
  subst y'
  exact CFGraphIso.vertexWedgeCongr_apply_left
    (CFGraphIso.refl G) phi x y a

/-- Reassociation data, including the endpoint fact needed to use the
isomorphism beneath a further vertex wedge. -/
structure MarkedChainReassocData (M F : Utilities.MarkedGraph)
    (rest : List Utilities.MarkedGraph) where
  /-- The graph isomorphism moving the first wedge outside the remaining chain. -/
  iso : CFGraphIso
    ((M.wedge F).chain rest).graph
    (M.wedge (F.chain rest)).graph
  map_left : iso.vertexEquiv ((M.wedge F).chain rest).left =
    (M.wedge (F.chain rest)).left

/-- Reassociate a left-associated marked chain so that its first factor is
glued to the chain of all remaining factors. -/
noncomputable def markedChainReassocData
    (M F : Utilities.MarkedGraph) :
    (rest : List Utilities.MarkedGraph) → MarkedChainReassocData M F rest
  | [] => {
      iso := CFGraphIso.refl (M.wedge F).graph
      map_left := rfl
    }
  | N :: rest => by
      let outer := markedChainReassocData (M.wedge F) N rest
      let inner := markedChainReassocData F N rest
      let assoc := vertexWedgeAssoc M.graph F.graph
        (N.chain rest).graph M.right F.left F.right (N.chain rest).left
      have hInnerLeft :
          inner.iso.symm.vertexEquiv (Sum.inl F.left) =
            ((F.wedge N).chain rest).left :=
        (inner.iso.vertexEquiv.symm_apply_eq).2 inner.map_left.symm
      let congr := vertexWedgeCongrRight inner.iso.symm M.right
        (Sum.inl F.left) ((F.wedge N).chain rest).left hInnerLeft
      refine {
        iso := outer.iso.trans (assoc.trans congr)
        map_left := ?_
      }
      change
        congr.vertexEquiv
            (assoc.vertexEquiv
              (outer.iso.vertexEquiv
                (((M.wedge F).wedge N).chain rest).left)) =
          Sum.inl M.left
      rw [outer.map_left]
      change congr.vertexEquiv
        (assoc.vertexEquiv (Sum.inl (Sum.inl M.left))) = Sum.inl M.left
      change congr.vertexEquiv (Sum.inl M.left) = Sum.inl M.left
      exact vertexWedgeCongrRight_apply_left inner.iso.symm M.right
        (Sum.inl F.left) ((F.wedge N).chain rest).left hInnerLeft M.left

/-- The graph isomorphism underlying `markedChainReassocData`. -/
noncomputable def markedChainReassocIso
    (M F : Utilities.MarkedGraph)
    (rest : List Utilities.MarkedGraph) :
    CFGraphIso ((M.wedge F).chain rest).graph
      (M.wedge (F.chain rest)).graph :=
  (markedChainReassocData M F rest).iso

@[simp] theorem markedChainReassocIso_apply_left
    (M F : Utilities.MarkedGraph)
    (rest : List Utilities.MarkedGraph) :
    (markedChainReassocIso M F rest).vertexEquiv
        ((M.wedge F).chain rest).left =
      (M.wedge (F.chain rest)).left :=
  (markedChainReassocData M F rest).map_left

/-! ## Reversing the right half of a chain -/

/-- Data for reversing a nonempty marked factor chain.  The isomorphism sends
the chain's left endpoint to the right endpoint of the outside-in presentation,
which is the central attachment vertex. -/
structure ReversedFactorChainIsoData
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) where
  /-- The graph isomorphism from the original chain to its reversed presentation. -/
  iso : CFGraphIso
    (F.marked.chain (rest.map KGeneralChainFactor.marked)).graph
    (reversedMarkedChain F rest).graph
  map_left : iso.vertexEquiv
      (F.marked.chain (rest.map KGeneralChainFactor.marked)).left =
    (reversedMarkedChain F rest).right

/-- The canonical chain of a list of factors is graph-isomorphic to its
outside-in reversed presentation with all marks swapped. -/
noncomputable def reversedFactorChainIsoData
    (F : KGeneralChainFactor) :
    (rest : List KGeneralChainFactor) → ReversedFactorChainIsoData F rest
  | [] => {
      iso := CFGraphIso.refl F.marked.graph
      map_left := rfl
    }
  | next :: rest => by
      let inner := reversedFactorChainIsoData next rest
      let assoc := markedChainReassocIso F.marked next.marked
        (rest.map KGeneralChainFactor.marked)
      have hInnerLeft :
          inner.iso.vertexEquiv
              (next.marked.chain (rest.map KGeneralChainFactor.marked)).left =
            (reversedMarkedChain next rest).right := inner.map_left
      let congr := vertexWedgeCongrRight inner.iso F.marked.right
        (next.marked.chain (rest.map KGeneralChainFactor.marked)).left
        (reversedMarkedChain next rest).right hInnerLeft
      let comm := vertexWedgeComm
        F.marked.graph (reversedMarkedChain next rest).graph
        F.marked.right (reversedMarkedChain next rest).right
      refine {
        iso := by
          simpa only [List.map_cons, MarkedGraph.chain_cons,
            reversedMarkedChain_cons, MarkedGraph.wedge,
            KGeneralChainFactor.swapMarks_graph,
            KGeneralChainFactor.swapMarks_left] using
            assoc.trans (congr.trans comm)
        map_left := ?_
      }
      change comm.vertexEquiv
        (congr.vertexEquiv
          (assoc.vertexEquiv
            ((F.marked.wedge next.marked).chain
              (rest.map KGeneralChainFactor.marked)).left)) =
          wedgeRightVertex (reversedMarkedChain next rest).graph F.marked.graph
            (reversedMarkedChain next rest).right F.marked.right F.marked.left
      rw [markedChainReassocIso_apply_left]
      change comm.vertexEquiv (congr.vertexEquiv (Sum.inl F.marked.left)) = _
      rw [vertexWedgeCongrRight_apply_left]
      exact vertexWedge_comm_apply_left
        F.marked.graph (reversedMarkedChain next rest).graph
        F.marked.right (reversedMarkedChain next rest).right F.marked.left

/-- The underlying graph isomorphism reversing the factor chain and interchanging its outer
marks. -/
noncomputable def reversedFactorChainIso
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    CFGraphIso
      (F.marked.chain (rest.map KGeneralChainFactor.marked)).graph
      (reversedMarkedChain F rest).graph :=
  (reversedFactorChainIsoData F rest).iso

@[simp] theorem reversedFactorChainIso_apply_left
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    (reversedFactorChainIso F rest).vertexEquiv
        (F.marked.chain (rest.map KGeneralChainFactor.marked)).left =
      (reversedMarkedChain F rest).right :=
  (reversedFactorChainIsoData F rest).map_left

/-! ## Corollary 6.16(2) for positive-genus chains -/

/-- The graph in the centered presentation of a balanced split is the
canonical left-associated chain, up to the explicit reassociation and reversal
isomorphisms above. -/
noncomputable def balancedChainGraphIso
    (leftHead : KGeneralChainFactor)
    (leftTail : List KGeneralChainFactor)
    (rightHead : KGeneralChainFactor)
    (rightTail : List KGeneralChainFactor) :
    CFGraphIso
      ((leftHead.marked.chain (leftTail.map KGeneralChainFactor.marked)).chain
        ((rightHead :: rightTail).map KGeneralChainFactor.marked)).graph
      (balancedChainGraph leftHead leftTail rightHead rightTail) := by
  let L := leftHead.marked.chain (leftTail.map KGeneralChainFactor.marked)
  let assoc := markedChainReassocIso L rightHead.marked
    (rightTail.map KGeneralChainFactor.marked)
  let reverse := reversedFactorChainIso rightHead rightTail
  let congr := vertexWedgeCongrRight reverse L.right
    (rightHead.marked.chain
      (rightTail.map KGeneralChainFactor.marked)).left
    (reversedMarkedChain rightHead rightTail).right
    (reversedFactorChainIso_apply_left rightHead rightTail)
  change CFGraphIso
    (L.chain ((rightHead :: rightTail).map KGeneralChainFactor.marked)).graph
    (vertexWedge L.graph (reversedMarkedChain rightHead rightTail).graph
      L.right (reversedMarkedChain rightHead rightTail).right)
  simpa only [List.map_cons, MarkedGraph.chain_cons] using assoc.trans congr

/-- **Corollary 6.16(2)** for chains of at least two positive-genus factors.

The paper's minimum prefix/suffix period bound chooses a nonempty balancing
cut.  The two once-marked halves are Brill--Noether general by the preceding
chain theorems; the centered wedge is general by Proposition 6.14, and the
explicit graph isomorphism transports that conclusion to the canonical chain.
-/
theorem brillNoetherGeneral_mixedTorsionChain_of_minBudget_of_positive
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hPositive : ∀ Q ∈ F :: next :: rest, 0 < genus Q.marked.graph)
    (hMin : ChainMinBudget (F :: next :: rest)) :
    BrillNoetherGeneral
      (F.marked.chain ((next :: rest).map KGeneralChainFactor.marked)).graph := by
  obtain ⟨leftHead, leftTail, rightHead, rightTail, hDecomp, hBalanced⟩ :=
    exists_chainBalancedAtSplit_of_minBudget_of_positive F next rest hPositive hMin
  have hCentered := brillNoetherGeneral_mixedTorsionChain_of_balancedSplit
    leftHead leftTail rightHead rightTail hBalanced
  have hTransport :=
    (brillNoetherGeneral_iff_graphIso
      (balancedChainGraphIso leftHead leftTail rightHead rightTail)).mp hCentered
  have hTail : next :: rest = leftTail ++ rightHead :: rightTail := by
    simpa using congrArg List.tail hDecomp
  have hHead : F = leftHead := by
    exact (List.cons.inj (by simpa only [List.cons_append] using hDecomp)).1
  rw [hTail, List.map_append, markedChain_append]
  rw [hHead]
  exact hTransport

/-! ## Absorbing genus-zero factors -/

/-- A genus-zero factor at the head of a canonical chain can be moved to the
right of the remaining chain and absorbed.  This is the graph-theoretic
reduction needed to extend Corollary 6.16(2) from positive-genus factors to
the paper's full graph convention. -/
theorem brillNoetherGeneral_factorChain_cons_genus_zero_of_tail
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hZero : genus F.marked.graph = 0)
    (hTail : BrillNoetherGeneral
      (next.marked.chain (rest.map KGeneralChainFactor.marked)).graph) :
    BrillNoetherGeneral
      (F.marked.chain ((next :: rest).map KGeneralChainFactor.marked)).graph := by
  let tail := next.marked.chain (rest.map KGeneralChainFactor.marked)
  let reassoc := markedChainReassocIso F.marked next.marked
    (rest.map KGeneralChainFactor.marked)
  let comm := vertexWedgeComm F.marked.graph tail.graph F.marked.right tail.left
  have hAbsorb : BrillNoetherGeneral
      (vertexWedge tail.graph F.marked.graph tail.left F.marked.right) :=
    brillNoetherGeneral_vertexWedge_genus_zero_right
      tail.graph F.marked.graph tail.left F.marked.right
      F.connected hZero hTail
  have hMove : BrillNoetherGeneral
      (vertexWedge F.marked.graph tail.graph F.marked.right tail.left) :=
    (brillNoetherGeneral_iff_graphIso comm).mp hAbsorb
  have hReassoc : BrillNoetherGeneral
      ((F.marked.wedge next.marked).chain
        (rest.map KGeneralChainFactor.marked)).graph :=
    (brillNoetherGeneral_iff_graphIso reassoc).mp hMove
  simpa only [List.map_cons, MarkedGraph.chain_cons] using hReassoc

/-- Once a marked accumulator is Brill--Noether general, appending only
connected genus-zero factors preserves Brill--Noether generality. -/
theorem brillNoetherGeneral_markedChain_of_tail_genus_zero
    (M : MarkedGraph) (tail : List KGeneralChainFactor)
    (hGeneral : BrillNoetherGeneral M.graph)
    (hZero : ∀ F ∈ tail, genus F.marked.graph = 0) :
    BrillNoetherGeneral
      (M.chain (tail.map KGeneralChainFactor.marked)).graph := by
  induction tail generalizing M with
  | nil => simpa using hGeneral
  | cons F rest ih =>
      rw [List.map_cons, MarkedGraph.chain_cons]
      apply ih (M.wedge F.marked)
      · exact brillNoetherGeneral_vertexWedge_genus_zero_right
          M.graph F.marked.graph M.right F.marked.left
          F.connected (hZero F (by simp)) hGeneral
      · intro Q hQ
        exact hZero Q (by simp [hQ])

/-- A single `k`-general factor is Brill--Noether general under the strict
genus-period bound appearing at an endpoint of Corollary 6.16(2). -/
private theorem brillNoetherGeneral_chainFactor_of_genus_lt_period
    (F : KGeneralChainFactor)
    (hBudget : genus F.marked.graph < (F.period : ℤ)) :
    BrillNoetherGeneral F.marked.graph := by
  let g : ℕ := (genus F.marked.graph).toNat
  have hGenusNonnegative : 0 ≤ genus F.marked.graph :=
    genus_nonneg_of_graph_connected F.marked.graph F.connected
  have hGenus : genus F.marked.graph = (g : ℤ) := by
    exact (Int.toNat_of_nonneg hGenusNonnegative).symm
  have hThreshold : g + 2 ≤ 2 * F.period := by
    have hPeriodPositive : 0 < F.period := F.kGeneral.1.1
    have hBudgetNat : g < F.period := by
      exact_mod_cast (hGenus ▸ hBudget)
    omega
  exact kGeneralTransmission_brillNoetherGeneral
    F.connected hGenus F.kGeneral hThreshold

/-- **Corollary 6.16(2)** in the paper's full graph convention, allowing
connected genus-zero factors in arbitrary positions.

At a nonzero first genus crossing, the canonical balancing argument applies
without any factorwise positivity assumption.  If the first crossing is
zero, nonnegativity forces the entire suffix to have genus zero; the minimum
budget makes the head factor general, and the suffix is absorbed one tree
factor at a time. -/
theorem brillNoetherGeneral_mixedTorsionChain_of_minBudget
    (F : KGeneralChainFactor) (tail : List KGeneralChainFactor)
    (hMin : ChainMinBudget (F :: tail)) :
    BrillNoetherGeneral
      (F.marked.chain (tail.map KGeneralChainFactor.marked)).graph := by
  cases tail with
  | nil =>
      apply brillNoetherGeneral_chainFactor_of_genus_lt_period F
      have h := hMin 0 (by simp)
      simpa [chainFactorGenus] using h
  | cons next rest =>
      by_cases hCrossingZero :
          firstGenusCrossing (F :: next :: rest) (by simp) = 0
      · have hCrossing :=
          firstGenusCrossing_spec (F :: next :: rest) (by simp)
        rw [hCrossingZero] at hCrossing
        have hTailNonnegative : 0 ≤ chainFactorGenus (next :: rest) :=
          chainFactorGenus_nonneg (next :: rest)
        have hCrossing' :
            genus F.marked.graph + chainFactorGenus (next :: rest) ≤
              genus F.marked.graph := by
          simpa only [List.drop_zero, List.take_succ_cons, List.take_zero,
            chainFactorGenus_cons, chainFactorGenus_nil, add_zero] using
              hCrossing
        have hTailSum : chainFactorGenus (next :: rest) = 0 := by
          exact le_antisymm (by omega) hTailNonnegative
        have hEveryTailZero :
            ∀ Q ∈ next :: rest, genus Q.marked.graph = 0 := by
          intro Q hQ
          exact genus_eq_zero_of_mem_of_chainFactorGenus_eq_zero
            (next :: rest) hTailSum Q hQ
        have hHeadBudget : genus F.marked.graph < (F.period : ℤ) := by
          have h := hMin 0 (by simp)
          simp only [List.take_succ_cons, List.take_zero, List.drop_zero,
            chainFactorGenus_cons, chainFactorGenus_nil, add_zero] at h
          have hTailSum' :
              genus next.marked.graph + chainFactorGenus rest = 0 := by
            simpa only [chainFactorGenus_cons] using hTailSum
          rw [hTailSum', add_zero, min_self] at h
          exact h
        exact brillNoetherGeneral_markedChain_of_tail_genus_zero
          F.marked (next :: rest)
          (brillNoetherGeneral_chainFactor_of_genus_lt_period F hHeadBudget)
          hEveryTailZero
      · have hCrossingPositive :
            0 < firstGenusCrossing (F :: next :: rest) (by simp) := by
          omega
        obtain ⟨leftHead, leftTail, rightHead, rightTail,
            hDecomp, hCross⟩ :=
          exists_chainDominatesAtSplit_of_firstCrossing_pos
            F next rest hCrossingPositive
        have hBalanced : ChainBalancedAtSplit
            (leftHead :: leftTail) (rightHead :: rightTail) := by
          apply chainBalancedAtSplit_of_minBudget
          · rwa [← hDecomp]
          · exact hCross
        have hCentered := brillNoetherGeneral_mixedTorsionChain_of_balancedSplit
          leftHead leftTail rightHead rightTail hBalanced
        have hTransport :=
          (brillNoetherGeneral_iff_graphIso
            (balancedChainGraphIso leftHead leftTail rightHead rightTail)).mp
              hCentered
        have hTail : next :: rest = leftTail ++ rightHead :: rightTail := by
          simpa using congrArg List.tail hDecomp
        have hHead : F = leftHead := by
          exact (List.cons.inj
            (by simpa only [List.cons_append] using hDecomp)).1
        rw [hTail, List.map_append, markedChain_append]
        rw [hHead]
        exact hTransport

end Bananas
