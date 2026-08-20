/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicWordReductionCore

/-!
# Marked finite cyclic word reduction

This file completes the recursive reduction developed in
`FiniteCyclicWordReductionCore`, carrying the marked normalization state through terminal block
normalization and the connected-presentation result.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

namespace Pairing

/-- Invariants carried by every marked normalization state. Protected-name uniqueness is stated on
name spines rather than dart-occurrence lists, so completed boundary carriers are counted once. -/
structure MarkedExecutionState {n : ℕ}
    (tokens : List (ReductionToken n)) where
  valid :
    (Dyck.oneFace
      (ReductionToken.expand tokens)).IsSurfaceValid
  separated : ReductionToken.IsSeparated tokens
  classified : ReductionToken.AllClassified tokens
  protectedNodup :
    (ReductionToken.protectedNames tokens).Nodup

namespace MarkedExecutionState

/-- The all-residual marking of a valid word satisfies every execution invariant. -/
theorem ofWord {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    MarkedExecutionState (ReductionToken.ofWord word) where
  valid := by simpa using valid
  separated := by
    rw [ReductionToken.IsSeparated]
    simp
  classified :=
    ReductionToken.allClassified_ofWord word
  protectedNodup := by
    simp

/-- Surface multiplicities restrict to the erased residual word because separation rules out any
residual name from all protected blocks. -/
theorem hasValidUsedMultiplicities_residualDarts {n : ℕ}
    {tokens : List (ReductionToken n)}
    (state : MarkedExecutionState tokens) :
    HasValidUsedMultiplicities
      (ReductionToken.residualDarts tokens) := by
  intro edge hedge
  have hnotProtected :
      edge ∉ ReductionToken.protectedEdges tokens := by
    intro hprotected
    exact (List.disjoint_left.mp state.separated)
      hedge hprotected
  rw [←
    ReductionToken.count_map_edgeOfDart_expand_eq_residualDarts_of_not_mem_protectedEdges
      tokens edge hnotProtected]
  simpa only [Dyck.oneFace_edgeMultiplicity] using
    state.valid.2.2.2 edge

end MarkedExecutionState

/-- Forget an actionable feature's occurrence decomposition while retaining its extracted block. -/
def ActionablePairReductionFeature.block {n : ℕ}
    {word : List (SignedDart (Fin n))} :
    ActionablePairReductionFeature word → ExtractedBlock n
  | .boundary a form => .boundary a form.negative
  | .crosscap a form => .crosscap a form.negative
  | .handle a b _ => .handle a b

namespace ActionablePairReductionFeature

/-- The edge names consumed by an actionable extraction. -/
def extractedEdges {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    List (Fin n) :=
  feature.block.edges

/-- Every actionable feature consumes at least one edge name. -/
theorem extractedEdges_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.extractedEdges ≠ [] := by
  cases feature <;>
    simp [extractedEdges, block, ExtractedBlock.edges]

/-- The edge names inside one extracted block are distinct. -/
theorem extractedEdges_nodup {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.extractedEdges.Nodup := by
  cases feature with
  | boundary => simp [extractedEdges, block, ExtractedBlock.edges]
  | crosscap => simp [extractedEdges, block, ExtractedBlock.edges]
  | handle a b form =>
      simp [extractedEdges, block, ExtractedBlock.edges,
        form.edge_ne]

/-- No edge consumed by a feature remains in its residual word. -/
theorem extractedEdges_disjoint_residualWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.extractedEdges.Disjoint
      (feature.residualWord.map edgeOfDart) := by
  cases feature with
  | boundary a form =>
      simpa [extractedEdges, block, ExtractedBlock.edges,
        residualWord] using form.edge_not_mem_remainder
  | crosscap a form =>
      simp [extractedEdges, block, ExtractedBlock.edges,
        residualWord, map_edgeOfDart_inverseWord,
        form.edge_not_mem_remainder,
        form.edge_not_mem_between]
  | handle a b form =>
      simp [extractedEdges, block, ExtractedBlock.edges,
        residualWord, form.a_not_mem_remainder,
        form.a_not_mem_beforeOutsideB,
        form.a_not_mem_beforeNegA,
        form.a_not_mem_beforeB,
        form.b_not_mem_remainder,
        form.b_not_mem_beforeOutsideB,
        form.b_not_mem_beforeNegA,
        form.b_not_mem_beforeB]

/-- Every name consumed by a feature occurs in its source word. -/
theorem extractedEdges_subset_source {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    ∀ e ∈ feature.extractedEdges, e ∈ word.map edgeOfDart := by
  intro e he
  cases feature with
  | boundary a form =>
      have hperm := (form.rotated.map edgeOfDart).perm
      rw [hperm.mem_iff]
      simp only [extractedEdges, block, ExtractedBlock.edges,
        List.mem_singleton] at he
      subst e
      simp
  | crosscap a form =>
      have hperm := (form.rotated.map edgeOfDart).perm
      rw [hperm.mem_iff]
      simp only [extractedEdges, block, ExtractedBlock.edges,
        List.mem_singleton] at he
      subst e
      simp
  | handle a b form =>
      have hperm := (form.rotated.map edgeOfDart).perm
      rw [hperm.mem_iff]
      simp only [extractedEdges, ExtractedBlock.edges, block, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp

end ActionablePairReductionFeature

/-- An actionable residual feature lifted to a marked word.  Extracted blocks occupy whole token
segments between the distinguished residual darts, so later rewrites can reorder or reverse those
segments without splitting a protected block. -/
inductive MarkedActionablePairReductionFeature {n : ℕ}
    (tokens : List (ReductionToken n))
  | boundary (a : Fin n)
      (form :
        BoundaryOccurrenceForm
          (ReductionToken.residualDarts tokens) a)
      (remainderTokens : List (ReductionToken n))
      (rotated :
        tokens.IsRotated
          (.residual (dart a form.negative) ::
            remainderTokens))
      (residual_remainder :
        ReductionToken.residualDarts remainderTokens =
          form.remainder)
  | crosscap (a : Fin n)
      (form :
        CrosscapOccurrenceForm
          (ReductionToken.residualDarts tokens) a)
      (betweenTokens remainderTokens :
        List (ReductionToken n))
      (rotated :
        tokens.IsRotated
          (.residual (dart a form.negative) ::
            betweenTokens ++
            .residual (dart a form.negative) ::
            remainderTokens))
      (residual_between :
        ReductionToken.residualDarts betweenTokens =
          form.between)
      (residual_remainder :
        ReductionToken.residualDarts remainderTokens =
          form.remainder)
  | handle (a b : Fin n)
      (form :
        InterleavedOccurrenceForm
          (ReductionToken.residualDarts tokens) a b)
      (beforeBTokens beforeNegATokens
        beforeOutsideBTokens remainderTokens :
        List (ReductionToken n))
      (rotated :
        tokens.IsRotated
          (.residual (.pos a) ::
            beforeBTokens ++
            .residual (dart b form.bNegativeInside) ::
            beforeNegATokens ++
            .residual (.neg a) ::
            beforeOutsideBTokens ++
            .residual (dart b (!form.bNegativeInside)) ::
            remainderTokens))
      (residual_beforeB :
        ReductionToken.residualDarts beforeBTokens =
          form.beforeB)
      (residual_beforeNegA :
        ReductionToken.residualDarts beforeNegATokens =
          form.beforeNegA)
      (residual_beforeOutsideB :
        ReductionToken.residualDarts beforeOutsideBTokens =
          form.beforeOutsideB)
      (residual_remainder :
        ReductionToken.residualDarts remainderTokens =
          form.remainder)

namespace MarkedActionablePairReductionFeature

/-- Residual feature underlying a marked feature. -/
def residualFeature {n : ℕ}
    {tokens : List (ReductionToken n)} :
    MarkedActionablePairReductionFeature tokens →
      ActionablePairReductionFeature
        (ReductionToken.residualDarts tokens)
  | .boundary a form _ _ _ => .boundary a form
  | .crosscap a form _ _ _ _ _ => .crosscap a form
  | .handle a b form _ _ _ _ _ _ _ _ _ =>
      .handle a b form

/-- Marked target: replace the distinguished residual darts by one atomic extracted block while
performing the same segment reversal/reordering as the local Gallier--Xu rewrite. -/
def targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)} :
    MarkedActionablePairReductionFeature tokens →
      List (ReductionToken n)
  | marked@(.boundary _ _ remainderTokens _ _) =>
      .extracted marked.residualFeature.block ::
        remainderTokens
  | .crosscap a form betweenTokens
      remainderTokens _ _ _ =>
      .completed (.crosscap a form.negative) ::
        ReductionToken.inverseSequence remainderTokens ++
        betweenTokens
  | .handle a b _ beforeBTokens
      beforeNegATokens beforeOutsideBTokens
      remainderTokens _ _ _ _ _ =>
      .completed (.handle a b) ::
        remainderTokens ++ beforeOutsideBTokens ++
        beforeNegATokens ++ beforeBTokens

private theorem targetTokens_ne_nil {n : ℕ} {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens) : marked.targetTokens ≠ [] := by
  cases marked <;> simp [targetTokens]

/-- Lift an actionable feature of the erased residual word to the marked token word. -/
noncomputable def lift {n : ℕ}
    {tokens : List (ReductionToken n)}
    (feature :
      ActionablePairReductionFeature
        (ReductionToken.residualDarts tokens)) :
    MarkedActionablePairReductionFeature tokens := by
  cases feature with
  | boundary a form =>
      let lifted :=
        ReductionToken.residualConsRotation
          tokens (dart a form.negative) form.remainder
          form.rotated
      exact .boundary a form lifted.tokenRemainder
        lifted.rotated lifted.residual_remainder
  | crosscap a form =>
      have hhead :
          (ReductionToken.residualDarts tokens).IsRotated
            (dart a form.negative ::
              (form.between ++
                dart a form.negative :: form.remainder)) := by
        simpa only [List.cons_append,
          List.append_assoc] using form.rotated
      let headLift :=
        ReductionToken.residualConsRotation
          tokens (dart a form.negative)
          (form.between ++
            dart a form.negative :: form.remainder)
          hhead
      let split :=
        ReductionToken.residualDartSplit
          headLift.tokenRemainder form.between
          form.remainder (dart a form.negative)
          headLift.residual_remainder
      have hrotated' :
          tokens.IsRotated
            (.residual (dart a form.negative) ::
              split.tokenLeft ++
              .residual (dart a form.negative) ::
              split.tokenRight) := by
        have hrotated := headLift.rotated
        rw [split.tokens_eq] at hrotated
        simpa only [List.cons_append,
          List.append_assoc] using hrotated
      exact .crosscap a form split.tokenLeft
        split.tokenRight hrotated'
        split.residual_left split.residual_right
  | handle a b form =>
      have hhead :
          (ReductionToken.residualDarts tokens).IsRotated
            (.pos a ::
              (form.beforeB ++
                dart b form.bNegativeInside ::
                form.beforeNegA ++
                .neg a ::
                form.beforeOutsideB ++
                dart b (!form.bNegativeInside) ::
                form.remainder)) := by
        simpa only [List.cons_append,
          List.append_assoc] using form.rotated
      let headLift :=
        ReductionToken.residualConsRotation
          tokens (.pos a)
          (form.beforeB ++
            dart b form.bNegativeInside ::
            form.beforeNegA ++
            .neg a ::
            form.beforeOutsideB ++
            dart b (!form.bNegativeInside) ::
            form.remainder)
          hhead
      let splitB :=
        ReductionToken.residualDartSplit
          headLift.tokenRemainder form.beforeB
          (form.beforeNegA ++
            .neg a ::
            form.beforeOutsideB ++
            dart b (!form.bNegativeInside) ::
            form.remainder)
          (dart b form.bNegativeInside)
          (by
            simpa only [List.cons_append,
              List.append_assoc] using
              headLift.residual_remainder)
      let splitNegA :=
        ReductionToken.residualDartSplit
          splitB.tokenRight form.beforeNegA
          (form.beforeOutsideB ++
            dart b (!form.bNegativeInside) ::
            form.remainder)
          (.neg a)
          (by
            simpa only [List.cons_append,
              List.append_assoc] using
              splitB.residual_right)
      let splitOutsideB :=
        ReductionToken.residualDartSplit
          splitNegA.tokenRight form.beforeOutsideB
          form.remainder
          (dart b (!form.bNegativeInside))
          splitNegA.residual_right
      have hrotated' :
          tokens.IsRotated
            (.residual (.pos a) ::
              splitB.tokenLeft ++
              .residual (dart b form.bNegativeInside) ::
              splitNegA.tokenLeft ++
              .residual (.neg a) ::
              splitOutsideB.tokenLeft ++
              .residual (dart b (!form.bNegativeInside)) ::
              splitOutsideB.tokenRight) := by
        have hrotated := headLift.rotated
        rw [splitB.tokens_eq, splitNegA.tokens_eq,
          splitOutsideB.tokens_eq] at hrotated
        simpa only [List.cons_append,
          List.append_assoc] using hrotated
      exact .handle a b form splitB.tokenLeft
        splitNegA.tokenLeft splitOutsideB.tokenLeft
        splitOutsideB.tokenRight hrotated'
        splitB.residual_left splitNegA.residual_left
        splitOutsideB.residual_left
        splitOutsideB.residual_right

/-- Erasing the marked target recovers exactly the residual word of the underlying feature. -/
theorem residualDarts_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens) :
    ReductionToken.residualDarts marked.targetTokens =
      marked.residualFeature.residualWord := by
  cases marked with
  | boundary a form remainderTokens _ hremainder =>
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.residualWord,
        hremainder]
  | crosscap a form betweenTokens remainderTokens
      _ hbetween hremainder =>
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.residualWord,
        hbetween, hremainder]
  | handle a b form beforeBTokens beforeNegATokens
      beforeOutsideBTokens remainderTokens _
      hbeforeB hbeforeNegA hbeforeOutsideB hremainder =>
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.residualWord,
        hbeforeB, hbeforeNegA, hbeforeOutsideB,
        hremainder, List.append_assoc]

/-- Marked extraction preserves the classified-token grammar. -/
theorem targetTokens_allClassified {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ReductionToken.AllClassified marked.targetTokens := by
  cases marked with
  | boundary a form remainderTokens rotated _ =>
      have displayed :=
        classified.of_isRotated rotated
      have remainderClassified :
          ReductionToken.AllClassified remainderTokens := by
        intro token htoken
        exact displayed token (by simp [htoken])
      rw [targetTokens,
        ReductionToken.allClassified_cons]
      exact ⟨trivial, remainderClassified⟩
  | crosscap a form betweenTokens remainderTokens
      rotated _ _ =>
      have displayed :=
        classified.of_isRotated rotated
      have betweenClassified :
          ReductionToken.AllClassified betweenTokens := by
        intro token htoken
        exact displayed token (by simp [htoken])
      have remainderClassified :
          ReductionToken.AllClassified remainderTokens := by
        intro token htoken
        exact displayed token (by simp [htoken])
      change ReductionToken.AllClassified
        ((.completed (.crosscap a form.negative) ::
            ReductionToken.inverseSequence remainderTokens) ++
          betweenTokens)
      apply ReductionToken.AllClassified.append
      · rw [ReductionToken.allClassified_cons]
        exact
          ⟨trivial,
            remainderClassified.inverseSequence⟩
      · exact betweenClassified
  | handle a b form beforeBTokens beforeNegATokens
      beforeOutsideBTokens remainderTokens rotated _ _ _ _ =>
      have displayed :=
        classified.of_isRotated rotated
      have beforeBClassified :
          ReductionToken.AllClassified beforeBTokens := by
        intro token htoken
        exact displayed token (by simp [htoken])
      have beforeNegAClassified :
          ReductionToken.AllClassified beforeNegATokens := by
        intro token htoken
        exact displayed token (by simp [htoken])
      have beforeOutsideBClassified :
          ReductionToken.AllClassified beforeOutsideBTokens := by
        intro token htoken
        exact displayed token (by simp [htoken])
      have remainderClassified :
          ReductionToken.AllClassified remainderTokens := by
        intro token htoken
        exact displayed token (by simp [htoken])
      change ReductionToken.AllClassified
        (((((.completed (.handle a b) ::
            remainderTokens) ++ beforeOutsideBTokens) ++
            beforeNegATokens) ++ beforeBTokens))
      exact
        (((by
              rw [ReductionToken.allClassified_cons]
              exact
                ⟨trivial, remainderClassified⟩ :
            ReductionToken.AllClassified
              (.completed (.handle a b) ::
                remainderTokens)).append
            beforeOutsideBClassified).append
          beforeNegAClassified).append
        beforeBClassified

/-- The protected names after one marked extraction are precisely the newly extracted names
together with the previously protected names. -/
theorem mem_protectedEdges_targetTokens_iff {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (e : Fin n) :
    e ∈ ReductionToken.protectedEdges marked.targetTokens ↔
      e ∈ marked.residualFeature.extractedEdges ∨
        e ∈ ReductionToken.protectedEdges tokens := by
  cases marked with
  | boundary a form remainderTokens rotated hremainder =>
      rw [(ReductionToken.protectedEdges_isRotated
        rotated).perm.mem_iff]
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.extractedEdges,
        ActionablePairReductionFeature.block,
        ExtractedBlock.edges]
  | crosscap a form betweenTokens remainderTokens
      rotated hbetween hremainder =>
      rw [(ReductionToken.protectedEdges_isRotated
        rotated).perm.mem_iff]
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.extractedEdges,
        ActionablePairReductionFeature.block,
        ExtractedBlock.edges, CompletedBlock.edges]
      tauto
  | handle a b form beforeBTokens beforeNegATokens
      beforeOutsideBTokens remainderTokens rotated
      hbeforeB hbeforeNegA hbeforeOutsideB hremainder =>
      rw [(ReductionToken.protectedEdges_isRotated
        rotated).perm.mem_iff]
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.extractedEdges,
        ActionablePairReductionFeature.block,
        ExtractedBlock.edges, CompletedBlock.edges]
      tauto

/-- A marked extraction prepends exactly its newly consumed names and otherwise only permutes the
existing protected-name spine. -/
theorem protectedNames_targetTokens_perm {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens) :
    (ReductionToken.protectedNames
      marked.targetTokens).Perm
        (marked.residualFeature.extractedEdges ++
          ReductionToken.protectedNames tokens) := by
  cases marked with
  | boundary a form remainderTokens rotated _ =>
      have hsource :
          (ReductionToken.protectedNames tokens).Perm
            (ReductionToken.protectedNames remainderTokens) := by
        simpa using
          (ReductionToken.protectedNames_isRotated
            rotated).perm
      simpa [targetTokens, residualFeature,
        ActionablePairReductionFeature.extractedEdges,
        ActionablePairReductionFeature.block,
        ExtractedBlock.edges] using
          List.Perm.cons a hsource.symm
  | crosscap a form betweenTokens remainderTokens
      rotated _ _ =>
      have hsource :
          (ReductionToken.protectedNames tokens).Perm
            (ReductionToken.protectedNames betweenTokens ++
              ReductionToken.protectedNames remainderTokens) := by
        simpa using
          (ReductionToken.protectedNames_isRotated
            rotated).perm
      have hinverse :=
        ReductionToken.protectedNames_inverseSequence_perm
          remainderTokens
      have hreorder :
          (ReductionToken.protectedNames
                (ReductionToken.inverseSequence remainderTokens) ++
              ReductionToken.protectedNames betweenTokens).Perm
            (ReductionToken.protectedNames tokens) :=
        (List.Perm.append hinverse
            (List.Perm.refl _)).trans
          (List.perm_append_comm.trans hsource.symm)
      simpa [targetTokens, residualFeature,
        ActionablePairReductionFeature.extractedEdges,
        ActionablePairReductionFeature.block,
        ExtractedBlock.edges, CompletedBlock.names,
        List.append_assoc] using
          List.Perm.cons a hreorder
  | handle a b form beforeBTokens beforeNegATokens
      beforeOutsideBTokens remainderTokens rotated _ _ _ _ =>
      have hsource :
          (ReductionToken.protectedNames tokens).Perm
            (ReductionToken.protectedNames beforeBTokens ++
              ReductionToken.protectedNames beforeNegATokens ++
              ReductionToken.protectedNames beforeOutsideBTokens ++
              ReductionToken.protectedNames remainderTokens) := by
        simpa [List.append_assoc] using
          (ReductionToken.protectedNames_isRotated
            rotated).perm
      let segments :=
        [ReductionToken.protectedNames beforeBTokens,
          ReductionToken.protectedNames beforeNegATokens,
          ReductionToken.protectedNames beforeOutsideBTokens,
          ReductionToken.protectedNames remainderTokens]
      have hsegments :
          ([ReductionToken.protectedNames remainderTokens,
              ReductionToken.protectedNames beforeOutsideBTokens,
              ReductionToken.protectedNames beforeNegATokens,
              ReductionToken.protectedNames beforeBTokens] :
            List (List (Fin n))).Perm segments := by
        simpa [segments] using List.reverse_perm segments
      have hreorder :
          (ReductionToken.protectedNames remainderTokens ++
              ReductionToken.protectedNames beforeOutsideBTokens ++
              ReductionToken.protectedNames beforeNegATokens ++
              ReductionToken.protectedNames beforeBTokens).Perm
            (ReductionToken.protectedNames tokens) := by
        have hflatten :=
          List.Perm.flatMap hsegments
            (f := id) (g := id)
            (fun _ _ => List.Perm.refl _)
        have hflatten' :
            (ReductionToken.protectedNames remainderTokens ++
                ReductionToken.protectedNames beforeOutsideBTokens ++
                ReductionToken.protectedNames beforeNegATokens ++
                ReductionToken.protectedNames beforeBTokens).Perm
              (ReductionToken.protectedNames beforeBTokens ++
                ReductionToken.protectedNames beforeNegATokens ++
                ReductionToken.protectedNames beforeOutsideBTokens ++
                ReductionToken.protectedNames remainderTokens) := by
          simpa [segments, List.flatMap,
            List.append_assoc] using hflatten
        exact hflatten'.trans hsource.symm
      simpa [targetTokens, residualFeature,
        ActionablePairReductionFeature.extractedEdges,
        ActionablePairReductionFeature.block,
        ExtractedBlock.edges, CompletedBlock.names,
        List.append_assoc] using
          (List.Perm.cons a (List.Perm.cons b hreorder))

/-- Every marked extraction creates at least one protected name. -/
theorem protectedNames_targetTokens_ne_nil {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens) :
    ReductionToken.protectedNames marked.targetTokens ≠ [] := by
  intro hnil
  obtain ⟨edge, hedge⟩ :=
    List.exists_mem_of_ne_nil
      marked.residualFeature.extractedEdges
      marked.residualFeature.extractedEdges_ne_nil
  have htarget :
      edge ∈
        ReductionToken.protectedNames
          marked.targetTokens :=
    marked.protectedNames_targetTokens_perm.mem_iff.mpr
      (List.mem_append.mpr (Or.inl hedge))
  simp [hnil] at htarget

/-- Extraction preserves global ownership uniqueness of protected names. -/
theorem targetTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames
      marked.targetTokens).Nodup := by
  apply marked.protectedNames_targetTokens_perm.nodup_iff.mpr
  rw [List.nodup_append]
  refine
    ⟨marked.residualFeature.extractedEdges_nodup,
      nodup, ?_⟩
  intro edge hnew oldEdge hold heq
  subst oldEdge
  have hresidual :
      edge ∈
        (ReductionToken.residualDarts tokens).map
          edgeOfDart :=
    marked.residualFeature.extractedEdges_subset_source
      edge hnew
  have hprotected :
      edge ∈ ReductionToken.protectedEdges tokens :=
    (ReductionToken.mem_protectedNames_iff_mem_protectedEdges
      tokens edge).mp hold
  exact (List.disjoint_left.mp separated)
    hresidual hprotected

/-- Marked extraction preserves separation of residual and protected edge namespaces. -/
theorem targetTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ReductionToken.IsSeparated marked.targetTokens := by
  rw [ReductionToken.IsSeparated, List.disjoint_left]
  intro e heResidual heProtected
  have heFeatureResidual :
      e ∈ marked.residualFeature.residualWord.map edgeOfDart := by
    simpa only [marked.residualDarts_targetTokens] using
      heResidual
  rw [marked.mem_protectedEdges_targetTokens_iff] at heProtected
  rcases heProtected with heNew | heOld
  · exact
      (List.disjoint_left.mp
        marked.residualFeature.extractedEdges_disjoint_residualWord)
        heNew heFeatureResidual
  · have heSourceResidual :
        e ∈
          (ReductionToken.residualDarts tokens).map
            edgeOfDart :=
      marked.residualFeature.mem_source_of_mem_residualWord
        e heFeatureResidual
    exact (List.disjoint_left.mp separated)
      heSourceResidual heOld

private theorem residualWord_disjoint_extractedEdges {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens) :
    List.Disjoint (marked.residualFeature.residualWord.map edgeOfDart)
      marked.residualFeature.extractedEdges :=
  marked.residualFeature.extractedEdges_disjoint_residualWord.symm

/-- Expanding a separated marked feature gives the genuine feature on the full signed word.
The separation invariant is exactly what rules out a selected residual edge from every protected
block lying in an intervening token segment. -/
def expandedFeature {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ActionablePairReductionFeature
      (ReductionToken.expand tokens) := by
  cases marked with
  | boundary a form remainderTokens rotated hremainder =>
      have separatedDisplayed :=
        separated.of_isRotated rotated
      have haResidual :
          a ∈
            (ReductionToken.residualDarts
              (.residual (dart a form.negative) ::
                remainderTokens)).map edgeOfDart := by
        simp
      have haProtected :=
        separatedDisplayed.not_mem_protected_of_mem_residual
          a haResidual
      refine .boundary a
        { negative := form.negative
          remainder := ReductionToken.expand remainderTokens
          rotated := ?_
          edge_not_mem_remainder := ?_ }
      · simpa only [ReductionToken.expand_cons,
          ReductionToken.word_residual,
          List.singleton_append] using
          ReductionToken.expand_isRotated rotated
      · rw [ReductionToken.mem_map_edgeOfDart_expand_iff]
        simp only [not_or]
        refine ⟨?_, ?_⟩
        · simpa only [hremainder] using
            form.edge_not_mem_remainder
        · intro ha
          apply haProtected
          simpa using ha
  | crosscap a form betweenTokens remainderTokens
      rotated hbetween hremainder =>
      have separatedDisplayed :=
        separated.of_isRotated rotated
      have haResidual :
          a ∈
            (ReductionToken.residualDarts
              (.residual (dart a form.negative) ::
                betweenTokens ++
                .residual (dart a form.negative) ::
                remainderTokens)).map edgeOfDart := by
        simp
      have haProtected :=
        separatedDisplayed.not_mem_protected_of_mem_residual
          a haResidual
      refine .crosscap a
        { negative := form.negative
          between := ReductionToken.expand betweenTokens
          remainder := ReductionToken.expand remainderTokens
          rotated := ?_
          edge_not_mem_between := ?_
          edge_not_mem_remainder := ?_ }
      · simpa only [ReductionToken.expand_cons,
          ReductionToken.word_residual,
          ReductionToken.expand_append,
          List.singleton_append, List.nil_append,
          List.cons_append,
          List.append_assoc] using
          ReductionToken.expand_isRotated rotated
      · rw [ReductionToken.mem_map_edgeOfDart_expand_iff]
        simp only [not_or]
        refine ⟨?_, ?_⟩
        · simpa only [hbetween] using
            form.edge_not_mem_between
        · intro ha
          apply haProtected
          simp only [ReductionToken.protectedEdges_cons,
            ReductionToken.extractedEdges_residual,
            List.nil_append,
            ReductionToken.protectedEdges_append,
            List.mem_append]
          exact Or.inl ha
      · rw [ReductionToken.mem_map_edgeOfDart_expand_iff]
        simp only [not_or]
        refine ⟨?_, ?_⟩
        · simpa only [hremainder] using
            form.edge_not_mem_remainder
        · intro ha
          apply haProtected
          simp only [ReductionToken.protectedEdges_cons,
            ReductionToken.extractedEdges_residual,
            List.nil_append,
            ReductionToken.protectedEdges_append,
            List.mem_append]
          exact Or.inr ha
  | handle a b form beforeBTokens beforeNegATokens
      beforeOutsideBTokens remainderTokens rotated
      hbeforeB hbeforeNegA hbeforeOutsideB hremainder =>
      have separatedDisplayed :=
        separated.of_isRotated rotated
      have haResidual :
          a ∈
            (ReductionToken.residualDarts
              (.residual (.pos a) ::
                beforeBTokens ++
                .residual (dart b form.bNegativeInside) ::
                beforeNegATokens ++
                .residual (.neg a) ::
                beforeOutsideBTokens ++
                .residual (dart b (!form.bNegativeInside)) ::
                remainderTokens)).map edgeOfDart := by
        simp
      have hbResidual :
          b ∈
            (ReductionToken.residualDarts
              (.residual (.pos a) ::
                beforeBTokens ++
                .residual (dart b form.bNegativeInside) ::
                beforeNegATokens ++
                .residual (.neg a) ::
                beforeOutsideBTokens ++
                .residual (dart b (!form.bNegativeInside)) ::
                remainderTokens)).map edgeOfDart := by
        simp
      have haProtected :=
        separatedDisplayed.not_mem_protected_of_mem_residual
          a haResidual
      have hbProtected :=
        separatedDisplayed.not_mem_protected_of_mem_residual
          b hbResidual
      have haBeforeB : a ∉ ReductionToken.protectedEdges beforeBTokens := by
        intro ha; exact haProtected (by simp [ha])
      have haBeforeNegA : a ∉ ReductionToken.protectedEdges beforeNegATokens := by
        intro ha; exact haProtected (by simp [ha])
      have haBeforeOutsideB :
          a ∉
            ReductionToken.protectedEdges
              beforeOutsideBTokens := by
        intro ha; exact haProtected (by simp [ha])
      have haRemainder : a ∉ ReductionToken.protectedEdges remainderTokens := by
        intro ha; exact haProtected (by simp [ha])
      have hbBeforeB : b ∉ ReductionToken.protectedEdges beforeBTokens := by
        intro hb; exact hbProtected (by simp [hb])
      have hbBeforeNegA : b ∉ ReductionToken.protectedEdges beforeNegATokens := by
        intro hb; exact hbProtected (by simp [hb])
      have hbBeforeOutsideB :
          b ∉
            ReductionToken.protectedEdges
              beforeOutsideBTokens := by
        intro hb; exact hbProtected (by simp [hb])
      have hbRemainder : b ∉ ReductionToken.protectedEdges remainderTokens := by
        intro hb; exact hbProtected (by simp [hb])
      refine .handle a b
        { bNegativeInside := form.bNegativeInside
          beforeB := ReductionToken.expand beforeBTokens
          beforeNegA := ReductionToken.expand beforeNegATokens
          beforeOutsideB :=
            ReductionToken.expand beforeOutsideBTokens
          remainder := ReductionToken.expand remainderTokens
          rotated := ?_
          edge_ne := form.edge_ne
          a_not_mem_beforeB := ?_
          a_not_mem_beforeNegA := ?_
          a_not_mem_beforeOutsideB := ?_
          a_not_mem_remainder := ?_
          b_not_mem_beforeB := ?_
          b_not_mem_beforeNegA := ?_
          b_not_mem_beforeOutsideB := ?_
          b_not_mem_remainder := ?_ }
      · simpa only [ReductionToken.expand_cons,
          ReductionToken.word_residual,
          ReductionToken.expand_append,
          List.singleton_append, List.nil_append,
          List.cons_append,
          List.append_assoc] using
          ReductionToken.expand_isRotated rotated
      all_goals
        rw [ReductionToken.mem_map_edgeOfDart_expand_iff]
        simp only [not_or]
      · exact ⟨by simpa only [hbeforeB] using
          form.a_not_mem_beforeB, haBeforeB⟩
      · exact ⟨by simpa only [hbeforeNegA] using
          form.a_not_mem_beforeNegA, haBeforeNegA⟩
      · exact ⟨by simpa only [hbeforeOutsideB] using
          form.a_not_mem_beforeOutsideB, haBeforeOutsideB⟩
      · exact ⟨by simpa only [hremainder] using
          form.a_not_mem_remainder, haRemainder⟩
      · exact ⟨by simpa only [hbeforeB] using
          form.b_not_mem_beforeB, hbBeforeB⟩
      · exact ⟨by simpa only [hbeforeNegA] using
          form.b_not_mem_beforeNegA, hbBeforeNegA⟩
      · exact ⟨by simpa only [hbeforeOutsideB] using
          form.b_not_mem_beforeOutsideB, hbBeforeOutsideB⟩
      · exact ⟨by simpa only [hremainder] using
          form.b_not_mem_remainder, hbRemainder⟩

/-- The full-word extraction target is exactly the expansion of the marked target. -/
theorem expandedFeature_block_word_append_residualWord {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    (marked.expandedFeature separated).block.word ++
        (marked.expandedFeature separated).residualWord =
      ReductionToken.expand marked.targetTokens := by
  cases marked with
  | boundary =>
      simp [expandedFeature, targetTokens,
        residualFeature,
        ActionablePairReductionFeature.block,
        ActionablePairReductionFeature.residualWord,
        ExtractedBlock.word]
  | crosscap =>
      simp [expandedFeature, targetTokens,
        ActionablePairReductionFeature.block,
        ActionablePairReductionFeature.residualWord,
        ExtractedBlock.word, CompletedBlock.word]
  | handle =>
      simp [expandedFeature, targetTokens,
        ActionablePairReductionFeature.block,
        ActionablePairReductionFeature.residualWord,
        ExtractedBlock.word, CompletedBlock.word,
        List.append_assoc]

end MarkedActionablePairReductionFeature

/-- An inverse pair which is adjacent at marked-token granularity.  Unlike adjacency only after
erasing protected blocks, this is immediately executable by the ordinary cancellation chain. -/
structure MarkedCancellablePair {n : ℕ}
    (tokens : List (ReductionToken (n + 1))) where
  /-- The `edge` declaration. -/
  edge : Fin (n + 1)
  /-- The `negativeFirst` declaration. -/
  negativeFirst : Bool
  /-- The `tailTokens` declaration. -/
  tailTokens : List (ReductionToken (n + 1))
  rotated :
    tokens.IsRotated
      (.residual (dart edge negativeFirst) ::
        .residual (dart edge (!negativeFirst)) ::
        tailTokens)

namespace MarkedCancellablePair

/-- Expanding a token-adjacent pair gives an ordinary cancellable pair on the full word. -/
def expandedPair {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedCancellablePair tokens) :
    CancellablePair (ReductionToken.expand tokens) where
  edge := pair.edge
  tail := ReductionToken.expand pair.tailTokens
  negativeFirst := pair.negativeFirst
  rotated := by
    have hrotated :=
      ReductionToken.expand_isRotated pair.rotated
    cases hnegative : pair.negativeFirst <;>
      simp only [dart, hnegative, Bool.not_false, Bool.not_true,
        ReductionToken.expand_cons, ReductionToken.word_residual, List.cons_append,
        List.nil_append, inversePair] at hrotated ⊢ <;>
      exact hrotated

/-- Validity ensures that the removed edge is absent from every remaining marked token. -/
theorem edge_not_mem_tailTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedCancellablePair tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    pair.edge ∉
      (ReductionToken.expand pair.tailTokens).map edgeOfDart :=
  pair.expandedPair.edge_not_mem_tail valid

/-- Separation of residual and protected names passes to the marked tail after deleting the
displayed residual pair. -/
theorem tailTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedCancellablePair tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ReductionToken.IsSeparated pair.tailTokens := by
  have separatedDisplayed :=
    separated.of_isRotated pair.rotated
  rw [ReductionToken.IsSeparated,
    List.disjoint_left] at separatedDisplayed ⊢
  intro e heResidual heProtected
  apply separatedDisplayed
  · simp only [ReductionToken.residualDarts_cons,
      ReductionToken.residualWord_residual,
      List.singleton_append, List.map_cons,
      edgeOfDart_dart, List.mem_cons]
    exact Or.inr (Or.inr heResidual)
  · simpa only [ReductionToken.protectedEdges_cons,
      ReductionToken.extractedEdges_residual,
      List.nil_append] using heProtected

/-- Removing a displayed residual pair leaves the protected-name spine unchanged up to rotation. -/
theorem tailTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedCancellablePair tokens)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames pair.tailTokens).Nodup := by
  have displayedNodup :=
    (ReductionToken.protectedNames_isRotated
      pair.rotated).nodup_iff.mp nodup
  simpa using displayedNodup

end MarkedCancellablePair

/-- A cancellable pair of the erased residual word lifted to its exact marked-token interval.
The intervening tokens have empty residual contribution but may contain protected blocks. -/
structure MarkedResidualCancellablePair {n : ℕ}
    (tokens : List (ReductionToken n)) where
  /-- The `edge` declaration. -/
  edge : Fin n
  /-- The `negativeFirst` declaration. -/
  negativeFirst : Bool
  /-- The `betweenTokens` declaration. -/
  betweenTokens : List (ReductionToken n)
  /-- The `tailTokens` declaration. -/
  tailTokens : List (ReductionToken n)
  rotated :
    tokens.IsRotated
      (.residual (dart edge negativeFirst) ::
        betweenTokens ++
        .residual (dart edge (!negativeFirst)) ::
        tailTokens)
  residual_between :
    ReductionToken.residualDarts betweenTokens = []

namespace MarkedResidualCancellablePair

/-- Lift an ordinary cancellable pair of the erased residual word to marked-token data. -/
noncomputable def lift {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair :
      CancellablePair
        (ReductionToken.residualDarts tokens)) :
    MarkedResidualCancellablePair tokens := by
  have hresidual :
      (ReductionToken.residualDarts tokens).IsRotated
        (dart pair.edge pair.negativeFirst ::
          dart pair.edge (!pair.negativeFirst) ::
          pair.tail) := by
    cases hnegative : pair.negativeFirst <;>
      simpa [inversePair, dart, hnegative] using
        pair.rotated
  let headLift :=
    ReductionToken.residualConsRotation
      tokens (dart pair.edge pair.negativeFirst)
      (dart pair.edge (!pair.negativeFirst) ::
        pair.tail)
      hresidual
  let split :=
    ReductionToken.residualDartSplit
      headLift.tokenRemainder [] pair.tail
      (dart pair.edge (!pair.negativeFirst))
      (by simpa using headLift.residual_remainder)
  have hrotated :
      tokens.IsRotated
        (.residual
            (dart pair.edge pair.negativeFirst) ::
          split.tokenLeft ++
          .residual
            (dart pair.edge (!pair.negativeFirst)) ::
          split.tokenRight) := by
    have h := headLift.rotated
    rw [split.tokens_eq] at h
    simpa only [List.cons_append,
      List.append_assoc] using h
  exact
    { edge := pair.edge
      negativeFirst := pair.negativeFirst
      betweenTokens := split.tokenLeft
      tailTokens := split.tokenRight
      rotated := hrotated
      residual_between := split.residual_left }

/-- When no protected token intervenes, a lifted residual pair is directly cancellable. -/
def toAdjacent {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (hempty : pair.betweenTokens = []) :
    MarkedCancellablePair tokens where
  edge := pair.edge
  negativeFirst := pair.negativeFirst
  tailTokens := pair.tailTokens
  rotated := by
    simpa [hempty] using pair.rotated

/-- Surface multiplicity ensures that a lifted pair's carrier occurs nowhere in its protected
interval or remaining marked tail. -/
theorem edge_not_mem_between_and_tail {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    pair.edge ∉
        (ReductionToken.expand pair.betweenTokens).map
          edgeOfDart ∧
      pair.edge ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart := by
  let displayed :=
    dart pair.edge pair.negativeFirst ::
      ReductionToken.expand pair.betweenTokens ++
      dart pair.edge (!pair.negativeFirst) ::
      ReductionToken.expand pair.tailTokens
  have hexpanded :
      (ReductionToken.expand tokens).IsRotated displayed := by
    simpa [displayed, ReductionToken.expand_cons,
      ReductionToken.expand_append,
      ReductionToken.word_residual,
      List.append_assoc] using
        ReductionToken.expand_isRotated pair.rotated
  have hmultiplicity := valid.2.2.2 pair.edge
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  have hcount :=
    (hexpanded.map edgeOfDart).perm.count_eq
      pair.edge
  have hdisplayed :
      (displayed.map edgeOfDart).count pair.edge = 2 := by
    have hlower :
        2 ≤
          (displayed.map edgeOfDart).count pair.edge := by
      simp [displayed]
      omega
    omega
  have hsum :
      (displayed.map edgeOfDart).count pair.edge =
        2 +
          ((ReductionToken.expand
              pair.betweenTokens).map
            edgeOfDart).count pair.edge +
          ((ReductionToken.expand
              pair.tailTokens).map
            edgeOfDart).count pair.edge := by
    simp [displayed]
    omega
  constructor
  · intro hmem
    have hpositive :
        0 <
          ((ReductionToken.expand
              pair.betweenTokens).map
            edgeOfDart).count pair.edge :=
      List.count_pos_iff.mpr hmem
    omega
  · intro hmem
    have hpositive :
        0 <
          ((ReductionToken.expand
              pair.tailTokens).map
            edgeOfDart).count pair.edge :=
      List.count_pos_iff.mpr hmem
    omega

/-- A lifted inverse pair contributes exactly two residual darts beyond its marked tail. -/
theorem residualDarts_length_eq {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens) :
    (ReductionToken.residualDarts tokens).length =
      2 +
        (ReductionToken.residualDarts
          pair.tailTokens).length := by
  have hlength :=
    (ReductionToken.residualEdges_isRotated
      pair.rotated).perm.length_eq
  simp [pair.residual_between] at hlength
  omega

end MarkedResidualCancellablePair

/-- A residual inverse pair surrounding one extracted boundary singleton.  Reclassifying the
three-token succession as one completed boundary block closes the singleton into the canonical
loop shape without changing the expanded cyclic presentation. -/
structure MarkedBoundaryClosure {n : ℕ}
    (tokens : List (ReductionToken n)) where
  /-- The `carrier` declaration. -/
  carrier : Fin n
  /-- The `hole` declaration. -/
  hole : Fin n
  /-- The `carrierNegative` declaration. -/
  carrierNegative : Bool
  /-- The `holeNegative` declaration. -/
  holeNegative : Bool
  /-- The `tailTokens` declaration. -/
  tailTokens : List (ReductionToken n)
  rotated :
    tokens.IsRotated
      (.residual (dart carrier carrierNegative) ::
        .extracted (.boundary hole holeNegative) ::
        .residual (dart carrier (!carrierNegative)) ::
        tailTokens)

namespace MarkedBoundaryClosure

/-- Exact three-dart spelling of the closed boundary loop. -/
def boundaryWord {n : ℕ} {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens) :
    List (SignedDart (Fin n)) :=
  [dart closure.carrier closure.carrierNegative,
    dart closure.hole closure.holeNegative,
    dart closure.carrier (!closure.carrierNegative)]

/-- Marked target obtained by replacing the displayed succession with one atomic protected word. -/
def targetTokens {n : ℕ} {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens) :
    List (ReductionToken n) :=
  .completed (.boundary closure.carrier closure.hole
    closure.carrierNegative closure.holeNegative) ::
    closure.tailTokens

/-- The source expansion is a cyclic rotation of the exact boundary-closure target expansion. -/
theorem expand_isRotated_target {n : ℕ}
    {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens) :
    (ReductionToken.expand tokens).IsRotated
      (ReductionToken.expand closure.targetTokens) := by
  have hexpanded :=
    ReductionToken.expand_isRotated closure.rotated
  simpa [targetTokens, boundaryWord,
    CompletedBlock.word, boundaryLoopWord,
    ExtractedBlock.word, dart] using hexpanded

/-- Boundary closure preserves the classified-token grammar. -/
theorem targetTokens_allClassified {n : ℕ}
    {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ReductionToken.AllClassified closure.targetTokens := by
  have displayed :=
    classified.of_isRotated closure.rotated
  have tailClassified :
      ReductionToken.AllClassified closure.tailTokens := by
    intro token htoken
    exact displayed token (by simp [htoken])
  rw [targetTokens,
    ReductionToken.allClassified_cons]
  exact ⟨trivial, tailClassified⟩

/-- Surface multiplicity forces the loop carrier to be absent from the remaining marked tail. -/
theorem carrier_not_mem_tail {n : ℕ}
    {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    closure.carrier ∉
      (ReductionToken.expand closure.tailTokens).map
        edgeOfDart := by
  have separatedDisplayed :=
    separated.of_isRotated closure.rotated
  have hcarrierResidual :
      closure.carrier ∈
        (ReductionToken.residualDarts
          (.residual
              (dart closure.carrier
                closure.carrierNegative) ::
            .extracted
              (.boundary closure.hole
                closure.holeNegative) ::
            .residual
              (dart closure.carrier
                (!closure.carrierNegative)) ::
            closure.tailTokens)).map edgeOfDart := by
    simp
  have hcarrierProtected :=
    separatedDisplayed.not_mem_protected_of_mem_residual
      closure.carrier hcarrierResidual
  have hcarrierHole : closure.carrier ≠ closure.hole := by
    intro heq
    apply hcarrierProtected
    simp [heq, ExtractedBlock.edges]
  have hcount :=
    (closure.expand_isRotated_target.map
      edgeOfDart).perm.count_eq closure.carrier
  have hmultiplicity := valid.2.2.2 closure.carrier
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  simp only [ReductionToken.expand_cons,
    ReductionToken.word_completed,
    CompletedBlock.word, boundaryLoopWord,
    List.map_append, List.map_cons, List.map_nil,
    edgeOfDart_dart, List.count_append,
    List.count_cons, List.count_nil,
    beq_self_eq_true, if_true,
    targetTokens] at hcount
  simp [hcarrierHole.symm] at hcount
  intro htail
  have hpositive :
      0 <
        ((ReductionToken.expand closure.tailTokens).map
          edgeOfDart).count closure.carrier :=
    List.count_pos_iff.mpr htail
  omega

/-- Closing a boundary singleton preserves separation of the remaining residual names from all
protected loop and block names. -/
theorem targetTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    ReductionToken.IsSeparated closure.targetTokens := by
  have separatedDisplayed :=
    separated.of_isRotated closure.rotated
  have hcarrierTail :=
    closure.carrier_not_mem_tail separated valid
  rw [ReductionToken.IsSeparated,
    List.disjoint_left]
  intro e heResidual heProtected
  have heResidualTail :
      e ∈
        (ReductionToken.residualDarts
          closure.tailTokens).map edgeOfDart := by
    simpa [targetTokens] using heResidual
  have heExpandedTail :
      e ∈
        (ReductionToken.expand
          closure.tailTokens).map edgeOfDart :=
    (ReductionToken.mem_map_edgeOfDart_expand_iff
      closure.tailTokens e).mpr (Or.inl heResidualTail)
  simp only [targetTokens,
    ReductionToken.protectedEdges_cons,
    ReductionToken.extractedEdges_completed,
    CompletedBlock.edges,
    List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at heProtected
  rcases heProtected with heBoundary | heProtectedTail
  · rcases heBoundary with rfl | rfl | rfl
    · exact hcarrierTail heExpandedTail
    · apply (List.disjoint_left.mp separatedDisplayed)
      · simp only [ReductionToken.residualDarts_cons,
          ReductionToken.residualWord_residual,
          ReductionToken.residualWord_extracted,
          List.singleton_append, List.nil_append,
          List.map_cons, edgeOfDart_dart,
          List.mem_cons]
        exact Or.inr (Or.inr heResidualTail)
      · simp [ReductionToken.protectedEdges_cons,
          ReductionToken.extractedEdges_residual,
          ReductionToken.extractedEdges_extracted,
          ExtractedBlock.edges]
    · exact hcarrierTail heExpandedTail
  · apply (List.disjoint_left.mp separatedDisplayed)
    · simp only [ReductionToken.residualDarts_cons,
        ReductionToken.residualWord_residual,
        ReductionToken.residualWord_extracted,
        List.singleton_append, List.nil_append,
        List.map_cons, edgeOfDart_dart,
        List.mem_cons]
      exact Or.inr (Or.inr heResidualTail)
    · simpa only [ReductionToken.protectedEdges_cons,
        ReductionToken.extractedEdges_residual,
        ReductionToken.extractedEdges_extracted,
        ExtractedBlock.edges, List.nil_append,
        List.singleton_append, List.mem_cons] using
          Or.inr heProtectedTail

/-- Closing a raw boundary singleton transfers its residual carrier into protected ownership
without duplicating any protected name. -/
theorem targetTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames
      closure.targetTokens).Nodup := by
  have displayedNodup :
      (ReductionToken.protectedNames
        (.residual
            (dart closure.carrier closure.carrierNegative) ::
          .extracted
              (.boundary closure.hole closure.holeNegative) ::
          .residual
              (dart closure.carrier
                (!closure.carrierNegative)) ::
          closure.tailTokens)).Nodup :=
    (ReductionToken.protectedNames_isRotated
      closure.rotated).nodup_iff.mp nodup
  have sourceFacts :
      closure.hole ∉
          ReductionToken.protectedNames closure.tailTokens ∧
        (ReductionToken.protectedNames
          closure.tailTokens).Nodup := by
    simpa [ExtractedBlock.edges] using displayedNodup
  have hcarrierHole : closure.carrier ≠ closure.hole := by
    intro heq
    have separatedDisplayed :=
      separated.of_isRotated closure.rotated
    exact
      (List.disjoint_left.mp separatedDisplayed)
        (a := closure.carrier)
        (by simp)
        (by simp [heq, ExtractedBlock.edges])
  have hcarrierTail :
      closure.carrier ∉
        ReductionToken.protectedNames
          closure.tailTokens := by
    intro hmem
    apply closure.carrier_not_mem_tail separated valid
    apply
      (ReductionToken.mem_map_edgeOfDart_expand_iff
        closure.tailTokens closure.carrier).mpr
    exact Or.inr
      ((ReductionToken.mem_protectedNames_iff_mem_protectedEdges
        closure.tailTokens closure.carrier).mp hmem)
  simpa [targetTokens, CompletedBlock.names,
    List.nodup_cons, hcarrierHole, hcarrierTail] using
      sourceFacts

end MarkedBoundaryClosure

/-- A raw boundary atom followed by a protected interval inside a residual inverse pair.  One
Dyck move rotates the raw atom behind that interval, exposing the next protected atom. -/
structure MarkedBoundaryAtomRotate {n : ℕ}
    (tokens : List (ReductionToken n)) where
  /-- The `carrier` declaration. -/
  carrier : Fin n
  /-- The `hole` declaration. -/
  hole : Fin n
  /-- The `carrierNegative` declaration. -/
  carrierNegative : Bool
  /-- The `holeNegative` declaration. -/
  holeNegative : Bool
  /-- The `insideTokens` declaration. -/
  insideTokens : List (ReductionToken n)
  /-- The `outsideTokens` declaration. -/
  outsideTokens : List (ReductionToken n)
  rotated :
    tokens.IsRotated
      (.residual (dart carrier carrierNegative) ::
        .extracted (.boundary hole holeNegative) ::
        insideTokens ++
        .residual (dart carrier (!carrierNegative)) ::
        outsideTokens)
  residual_inside :
    ReductionToken.residualDarts insideTokens = []
  carrier_ne_hole : carrier ≠ hole
  carrier_not_mem_inside :
    carrier ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  carrier_not_mem_outside :
    carrier ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart

namespace MarkedBoundaryAtomRotate

/-- Exact marked target of moving the raw boundary atom to the end of its protected interval. -/
def targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens) :
    List (ReductionToken n) :=
  .residual (dart step.carrier step.carrierNegative) ::
    step.insideTokens ++
    .extracted (.boundary step.hole step.holeNegative) ::
    .residual (dart step.carrier
      (!step.carrierNegative)) ::
    step.outsideTokens

/-- Boundary-atom rotation only permutes atomic marked tokens. -/
theorem perm_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens) :
    tokens.Perm step.targetTokens := by
  let raw : ReductionToken n :=
    .extracted (.boundary step.hole step.holeNegative)
  let suffix : List (ReductionToken n) :=
    .residual
        (dart step.carrier (!step.carrierNegative)) ::
      step.outsideTokens
  have hmove :
      (raw :: step.insideTokens ++ suffix).Perm
        (step.insideTokens ++ raw :: suffix) := by
    have hswap :
        ([raw] ++ step.insideTokens).Perm
          (step.insideTokens ++ [raw]) :=
      List.perm_append_comm
    simpa [suffix, List.append_assoc] using
      hswap.append_right suffix
  apply step.rotated.perm.trans
  simpa [targetTokens, raw, suffix,
    List.append_assoc] using
      List.Perm.cons
        (.residual
          (dart step.carrier step.carrierNegative))
        hmove

/-- Expansion of the marked source has the word-level boundary-atom rotation spelling. -/
theorem expand_isRotated_sourceWord {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens) :
    (ReductionToken.expand tokens).IsRotated
      (BoundaryAtomRotate.sourceWord
        step.carrier step.hole step.carrierNegative
        step.holeNegative
        (ReductionToken.expand step.insideTokens)
        (ReductionToken.expand step.outsideTokens)) := by
  simpa [BoundaryAtomRotate.sourceWord,
    ReductionToken.expand_cons,
    ReductionToken.expand_append,
    ReductionToken.word_residual,
    ReductionToken.word_extracted,
    ExtractedBlock.word, List.append_assoc] using
      ReductionToken.expand_isRotated step.rotated

/-- Expansion of the exact marked target is the word-level rotation target. -/
theorem expand_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens) :
    ReductionToken.expand step.targetTokens =
      BoundaryAtomRotate.targetWord
        step.carrier step.hole step.carrierNegative
        step.holeNegative
        (ReductionToken.expand step.insideTokens)
        (ReductionToken.expand step.outsideTokens) := by
  simp [targetTokens, BoundaryAtomRotate.targetWord,
    ReductionToken.expand_cons,
    ReductionToken.expand_append,
    ReductionToken.word_residual,
    ReductionToken.word_extracted,
    ExtractedBlock.word]

theorem targetTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ReductionToken.IsSeparated step.targetTokens :=
  separated.of_perm step.perm_targetTokens

theorem targetTokens_allClassified {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ReductionToken.AllClassified step.targetTokens :=
  classified.of_perm step.perm_targetTokens

theorem targetTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames
      step.targetTokens).Nodup :=
  ReductionToken.protectedNames_nodup_of_perm
    nodup step.perm_targetTokens

/-- The same residual pair surrounds the rotated protected interval at the exact marked target. -/
def targetPair {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens) :
    MarkedResidualCancellablePair step.targetTokens where
  edge := step.carrier
  negativeFirst := step.carrierNegative
  betweenTokens :=
    step.insideTokens ++
      [.extracted
        (.boundary step.hole step.holeNegative)]
  tailTokens := step.outsideTokens
  rotated := by
    simpa [targetTokens, List.append_assoc] using
      (List.IsRotated.refl step.targetTokens)
  residual_between := by
    simp [step.residual_inside]

end MarkedBoundaryAtomRotate

/-- A completed boundary-loop atom at the head of a protected residual-pair interval.  One
`LoopGrouping` move commutes this atom out of that interval. -/
structure MarkedBoundaryBlockCommute {n : ℕ}
    (tokens : List (ReductionToken n)) where
  /-- The `outer` declaration. -/
  outer : Fin n
  /-- The `carrier` declaration. -/
  carrier : Fin n
  /-- The `hole` declaration. -/
  hole : Fin n
  /-- The `outerNegative` declaration. -/
  outerNegative : Bool
  /-- The `carrierNegative` declaration. -/
  carrierNegative : Bool
  /-- The `holeNegative` declaration. -/
  holeNegative : Bool
  /-- The `insideTokens` declaration. -/
  insideTokens : List (ReductionToken n)
  /-- The `outsideTokens` declaration. -/
  outsideTokens : List (ReductionToken n)
  rotated :
    tokens.IsRotated
      (.residual (dart outer outerNegative) ::
        .completed (.boundary carrier hole
          carrierNegative holeNegative) ::
        insideTokens ++
        .residual (dart outer (!outerNegative)) ::
        outsideTokens)
  carrier_ne_hole : carrier ≠ hole
  carrier_ne_outer : carrier ≠ outer
  carrier_not_mem_inside :
    carrier ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  carrier_not_mem_outside :
    carrier ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart

namespace MarkedBoundaryBlockCommute

/-- Exact marked target after commuting the completed boundary loop out of the residual pair. -/
def targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens) :
    List (ReductionToken n) :=
  .completed (.boundary commute.carrier commute.hole
      commute.carrierNegative commute.holeNegative) ::
    .residual (dart commute.outer commute.outerNegative) ::
    commute.insideTokens ++
    .residual (dart commute.outer
      (!commute.outerNegative)) ::
    commute.outsideTokens

/-- The commute target merely permutes atomic marked tokens. -/
theorem perm_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens) :
    tokens.Perm commute.targetTokens := by
  apply commute.rotated.perm.trans
  simpa [targetTokens] using
    (List.Perm.swap
      (.residual
        (dart commute.outer commute.outerNegative))
      (.completed
        (.boundary commute.carrier commute.hole
          commute.carrierNegative commute.holeNegative))
      (commute.insideTokens ++
        .residual
          (dart commute.outer
            (!commute.outerNegative)) ::
        commute.outsideTokens)).symm

/-- Expansion of the marked source has exactly the word-level boundary-block commute spelling. -/
theorem expand_isRotated_sourceWord {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens) :
    (ReductionToken.expand tokens).IsRotated
      (if commute.carrierNegative then
        BoundaryBlockCommute.negativeSourceWord
          commute.outer commute.carrier commute.hole
          commute.outerNegative commute.holeNegative
          (ReductionToken.expand commute.insideTokens)
          (ReductionToken.expand commute.outsideTokens)
      else
        BoundaryBlockCommute.sourceWord
          commute.outer commute.carrier commute.hole
          commute.outerNegative commute.holeNegative
          (ReductionToken.expand commute.insideTokens)
          (ReductionToken.expand commute.outsideTokens)) := by
  have hexpanded :=
    ReductionToken.expand_isRotated commute.rotated
  cases hnegative : commute.carrierNegative <;>
    simpa [hnegative, BoundaryBlockCommute.sourceWord,
      BoundaryBlockCommute.negativeSourceWord,
      ReductionToken.expand_cons,
      ReductionToken.expand_append,
      ReductionToken.word_residual,
      ReductionToken.word_completed,
      CompletedBlock.word, List.append_assoc] using
      hexpanded

/-- Expansion of the exact marked target is the word-level commute target. -/
theorem expand_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens) :
    ReductionToken.expand commute.targetTokens =
      if commute.carrierNegative then
        BoundaryBlockCommute.negativeTargetWord
          commute.outer commute.carrier commute.hole
          commute.outerNegative commute.holeNegative
          (ReductionToken.expand commute.insideTokens)
          (ReductionToken.expand commute.outsideTokens)
      else
        BoundaryBlockCommute.targetWord
          commute.outer commute.carrier commute.hole
          commute.outerNegative commute.holeNegative
          (ReductionToken.expand commute.insideTokens)
          (ReductionToken.expand commute.outsideTokens) := by
  cases hnegative : commute.carrierNegative <;>
    simp [targetTokens, hnegative,
      BoundaryBlockCommute.targetWord,
      BoundaryBlockCommute.negativeTargetWord,
      ReductionToken.expand_cons,
      ReductionToken.expand_append,
      ReductionToken.word_residual,
      ReductionToken.word_completed,
      CompletedBlock.word, List.append_assoc]

/-- Boundary-block commuting preserves the separated namespace invariant. -/
theorem targetTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ReductionToken.IsSeparated commute.targetTokens :=
  separated.of_perm commute.perm_targetTokens

/-- Boundary-block commuting preserves the classified-token grammar. -/
theorem targetTokens_allClassified {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ReductionToken.AllClassified commute.targetTokens :=
  classified.of_perm commute.perm_targetTokens

/-- Boundary-loop commuting preserves unique ownership of protected names. -/
theorem targetTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames
      commute.targetTokens).Nodup :=
  ReductionToken.protectedNames_nodup_of_perm
    nodup commute.perm_targetTokens

end MarkedBoundaryBlockCommute

/-- A completed crosscap at the head of a protected residual-pair interval.  Commuting it through
the pair exchanges the residual and completed carriers and shortens that protected interval. -/
structure MarkedCrosscapBlockCommute {n : ℕ}
    (tokens : List (ReductionToken n)) where
  /-- The `outer` declaration. -/
  outer : Fin n
  /-- The `carrier` declaration. -/
  carrier : Fin n
  /-- The `outerNegative` declaration. -/
  outerNegative : Bool
  /-- The `carrierNegative` declaration. -/
  carrierNegative : Bool
  /-- The `insideTokens` declaration. -/
  insideTokens : List (ReductionToken n)
  /-- The `outsideTokens` declaration. -/
  outsideTokens : List (ReductionToken n)
  rotated :
    tokens.IsRotated
      (.residual (dart outer outerNegative) ::
        .completed (.crosscap carrier carrierNegative) ::
        insideTokens ++
        .residual (dart outer (!outerNegative)) ::
        outsideTokens)
  carrier_ne_outer : carrier ≠ outer
  carrier_not_mem_inside :
    carrier ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  carrier_not_mem_outside :
    carrier ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart
  outer_not_mem_inside :
    outer ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  outer_not_mem_outside :
    outer ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart

namespace MarkedCrosscapBlockCommute

/-- Exact marked target of contextual crosscap commuting. -/
def targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedCrosscapBlockCommute tokens) :
    List (ReductionToken n) :=
  .completed (.crosscap commute.outer
      commute.outerNegative) ::
    .residual
      (dart commute.carrier
        (!commute.carrierNegative)) ::
    commute.insideTokens ++
    .residual
      (dart commute.carrier
        commute.carrierNegative) ::
    ReductionToken.inverseSequence
      commute.outsideTokens

/-- Expansion of the marked source is the generic contextual crosscap source spelling. -/
theorem expand_isRotated_sourceWord {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedCrosscapBlockCommute tokens) :
    (ReductionToken.expand tokens).IsRotated
      (CrosscapBlockCommute.sourceWord
        commute.outer commute.carrier
        commute.outerNegative commute.carrierNegative
        (ReductionToken.expand commute.insideTokens)
        (ReductionToken.expand
          commute.outsideTokens)) := by
  have hexpanded :=
    ReductionToken.expand_isRotated commute.rotated
  simpa [CrosscapBlockCommute.sourceWord,
    ReductionToken.expand_cons,
    ReductionToken.expand_append,
    ReductionToken.word_residual,
    ReductionToken.word_completed,
    CompletedBlock.word, List.append_assoc] using
    hexpanded

/-- Expansion of the exact marked target is the generic contextual crosscap target spelling. -/
theorem expand_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedCrosscapBlockCommute tokens) :
    ReductionToken.expand commute.targetTokens =
      CrosscapBlockCommute.targetWord
        commute.outer commute.carrier
        commute.outerNegative commute.carrierNegative
        (ReductionToken.expand commute.insideTokens)
        (ReductionToken.expand
          commute.outsideTokens) := by
  simp [targetTokens, CrosscapBlockCommute.targetWord,
    ReductionToken.expand_cons,
    ReductionToken.expand_append,
    ReductionToken.word_residual,
    ReductionToken.word_completed,
    CompletedBlock.word]

/-- Contextual crosscap commuting preserves the classified-token grammar. -/
theorem targetTokens_allClassified {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedCrosscapBlockCommute tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ReductionToken.AllClassified commute.targetTokens := by
  have displayed :=
    classified.of_isRotated commute.rotated
  have insideClassified :
      ReductionToken.AllClassified
        commute.insideTokens := by
    intro token htoken
    exact displayed token (by simp [htoken])
  have outsideClassified :
      ReductionToken.AllClassified
        commute.outsideTokens := by
    intro token htoken
    exact displayed token (by simp [htoken])
  intro token htoken
  simp only [targetTokens, List.mem_cons,
    List.mem_append] at htoken
  rcases htoken with (rfl | rfl | hinside) |
      rfl | houtside
  · trivial
  · trivial
  · exact insideClassified token hinside
  · trivial
  · exact outsideClassified.inverseSequence
      token houtside

/-- Contextual crosscap commuting preserves separation of residual and protected edge names. -/
theorem targetTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedCrosscapBlockCommute tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ReductionToken.IsSeparated commute.targetTokens := by
  let displayedTokens :=
    .residual
        (dart commute.outer commute.outerNegative) ::
      .completed
        (.crosscap commute.carrier
          commute.carrierNegative) ::
      commute.insideTokens ++
      .residual
        (dart commute.outer
          (!commute.outerNegative)) ::
      commute.outsideTokens
  have separatedDisplayed :
      ReductionToken.IsSeparated displayedTokens := by
    exact separated.of_isRotated commute.rotated
  rw [ReductionToken.IsSeparated,
    List.disjoint_left]
  intro edge heResidual heProtected
  have hresidual :
      edge = commute.carrier ∨
        edge ∈
          (ReductionToken.residualDarts
            commute.insideTokens).map edgeOfDart ∨
        edge ∈
          (ReductionToken.residualDarts
            commute.outsideTokens).map edgeOfDart := by
    have hraw := heResidual
    simp only [targetTokens, List.cons_append, ReductionToken.residualDarts_cons,
      ReductionToken.residualWord_completed, ReductionToken.residualWord_residual,
      ReductionToken.residualDarts_append, ReductionToken.residualDarts_inverseSequence,
      List.nil_append, List.map_cons, edgeOfDart_dart, List.map_append,
      map_edgeOfDart_inverseWord, List.mem_cons, List.mem_append, List.mem_map,
      List.mem_reverse] at hraw
    rcases hraw with hcarrier | hinside |
        hcarrier | houtside
    · exact Or.inl hcarrier
    · rcases hinside with ⟨dart, hdart, rfl⟩
      exact Or.inr (Or.inl
        (List.mem_map.mpr ⟨dart, hdart, rfl⟩))
    · exact Or.inl hcarrier
    · rcases houtside with ⟨dart, hdart, rfl⟩
      exact Or.inr (Or.inr
        (List.mem_map.mpr ⟨dart, hdart, rfl⟩))
  have hprotected :
      edge = commute.outer ∨
        edge ∈
          ReductionToken.protectedEdges
            commute.insideTokens ∨
        edge ∈
          ReductionToken.protectedEdges
            commute.outsideTokens := by
    simpa [targetTokens, CompletedBlock.edges] using
      heProtected
  have sourceDisjoint
      (hresidual :
        edge ∈
            (ReductionToken.residualDarts
              commute.insideTokens).map edgeOfDart ∨
          edge ∈
            (ReductionToken.residualDarts
              commute.outsideTokens).map edgeOfDart)
      (hprotected :
        edge ∈
            ReductionToken.protectedEdges
              commute.insideTokens ∨
          edge ∈
            ReductionToken.protectedEdges
              commute.outsideTokens) :
      False := by
    have heDisplayedResidual :
        edge ∈
          (ReductionToken.residualDarts
            displayedTokens).map edgeOfDart := by
      simp only [displayedTokens,
        ReductionToken.residualDarts_cons,
        ReductionToken.residualDarts_append,
        ReductionToken.residualWord_residual,
        ReductionToken.residualWord_completed,
        List.singleton_append, List.nil_append,
        List.map_cons, List.map_append,
        List.mem_cons, List.mem_append,
        edgeOfDart_dart]
      tauto
    have heDisplayedProtected :
        edge ∈
          ReductionToken.protectedEdges
            displayedTokens := by
      simp only [displayedTokens,
        ReductionToken.protectedEdges_cons,
        ReductionToken.protectedEdges_append,
        ReductionToken.extractedEdges_residual,
        ReductionToken.extractedEdges_completed,
        CompletedBlock.edges,
        List.nil_append, List.singleton_append,
        List.mem_cons, List.mem_append]
      tauto
    exact (List.disjoint_left.mp separatedDisplayed)
      heDisplayedResidual heDisplayedProtected
  rcases hresidual with rfl | hresidual
  · rcases hprotected with hcarrierOuter |
        hcarrierProtected
    · exact commute.carrier_ne_outer hcarrierOuter
    · rcases hcarrierProtected with hinside | houtside
      · exact commute.carrier_not_mem_inside
          ((ReductionToken.mem_map_edgeOfDart_expand_iff
            commute.insideTokens commute.carrier).mpr
            (Or.inr hinside))
      · exact commute.carrier_not_mem_outside
          ((ReductionToken.mem_map_edgeOfDart_expand_iff
            commute.outsideTokens commute.carrier).mpr
            (Or.inr houtside))
  · rcases hresidual with hinsideResidual |
        houtsideResidual
    · rcases hprotected with houter | hprotected
      · subst edge
        exact commute.outer_not_mem_inside
          ((ReductionToken.mem_map_edgeOfDart_expand_iff
            commute.insideTokens commute.outer).mpr
            (Or.inl hinsideResidual))
      · rcases hprotected with hinsideProtected |
          houtsideProtected
        · exact sourceDisjoint
            (Or.inl hinsideResidual)
            (Or.inl hinsideProtected)
        · exact sourceDisjoint
            (Or.inl hinsideResidual)
            (Or.inr houtsideProtected)
    · rcases hprotected with houter | hprotected
      · subst edge
        exact commute.outer_not_mem_outside
          ((ReductionToken.mem_map_edgeOfDart_expand_iff
            commute.outsideTokens commute.outer).mpr
            (Or.inl houtsideResidual))
      · rcases hprotected with hinsideProtected |
          houtsideProtected
        · exact sourceDisjoint
            (Or.inr houtsideResidual)
            (Or.inl hinsideProtected)
        · exact sourceDisjoint
            (Or.inr houtsideResidual)
            (Or.inr houtsideProtected)

/-- Crosscap commuting exchanges a protected carrier with a fresh residual carrier while
preserving unique protected-name ownership. -/
theorem targetTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedCrosscapBlockCommute tokens)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames
      commute.targetTokens).Nodup := by
  let displayedTokens :=
    .residual
        (dart commute.outer commute.outerNegative) ::
      .completed
        (.crosscap commute.carrier
          commute.carrierNegative) ::
      commute.insideTokens ++
      .residual
        (dart commute.outer
          (!commute.outerNegative)) ::
      commute.outsideTokens
  have displayedNodup :
      (ReductionToken.protectedNames
        displayedTokens).Nodup :=
    (ReductionToken.protectedNames_isRotated
      commute.rotated).nodup_iff.mp nodup
  have oldTailNodup :
      (ReductionToken.protectedNames
          commute.insideTokens ++
        ReductionToken.protectedNames
          commute.outsideTokens).Nodup := by
    have sourceFacts :
        (commute.carrier ::
          (ReductionToken.protectedNames
              commute.insideTokens ++
            ReductionToken.protectedNames
              commute.outsideTokens)).Nodup := by
      simpa [displayedTokens,
        CompletedBlock.names, List.append_assoc] using
          displayedNodup
    exact sourceFacts.tail
  have suffixPerm :
      (ReductionToken.protectedNames
          commute.insideTokens ++
        ReductionToken.protectedNames
          (ReductionToken.inverseSequence
            commute.outsideTokens)).Perm
      (ReductionToken.protectedNames
          commute.insideTokens ++
        ReductionToken.protectedNames
          commute.outsideTokens) :=
    List.Perm.append (List.Perm.refl _)
      (ReductionToken.protectedNames_inverseSequence_perm
        commute.outsideTokens)
  have suffixNodup :=
    suffixPerm.nodup_iff.mpr oldTailNodup
  have houterSuffix :
      commute.outer ∉
        ReductionToken.protectedNames
            commute.insideTokens ++
          ReductionToken.protectedNames
            (ReductionToken.inverseSequence
              commute.outsideTokens) := by
    rw [List.mem_append, not_or]
    refine ⟨?_, ?_⟩
    · intro hmem
      apply commute.outer_not_mem_inside
      apply
        (ReductionToken.mem_map_edgeOfDart_expand_iff
          commute.insideTokens commute.outer).mpr
      exact Or.inr
        ((ReductionToken.mem_protectedNames_iff_mem_protectedEdges
          commute.insideTokens commute.outer).mp hmem)
    · intro hmem
      have houtsideNames :
          commute.outer ∈
            ReductionToken.protectedNames
              commute.outsideTokens :=
        (ReductionToken.protectedNames_inverseSequence_perm
          commute.outsideTokens).mem_iff.mp hmem
      apply commute.outer_not_mem_outside
      apply
        (ReductionToken.mem_map_edgeOfDart_expand_iff
          commute.outsideTokens commute.outer).mpr
      exact Or.inr
        ((ReductionToken.mem_protectedNames_iff_mem_protectedEdges
          commute.outsideTokens commute.outer).mp
            houtsideNames)
  simpa [targetTokens, CompletedBlock.names,
    List.append_assoc] using
      (List.nodup_cons.mpr
        ⟨houterSuffix, suffixNodup⟩)

end MarkedCrosscapBlockCommute

/-- A completed handle at the head of a protected residual-pair interval. -/
structure MarkedHandleBlockCommute {n : ℕ}
    (tokens : List (ReductionToken n)) where
  /-- The `outer` declaration. -/
  outer : Fin n
  /-- The `first` declaration. -/
  first : Fin n
  /-- The `second` declaration. -/
  second : Fin n
  /-- The `outerNegative` declaration. -/
  outerNegative : Bool
  /-- The `insideTokens` declaration. -/
  insideTokens : List (ReductionToken n)
  /-- The `outsideTokens` declaration. -/
  outsideTokens : List (ReductionToken n)
  rotated :
    tokens.IsRotated
      (.residual (dart outer outerNegative) ::
        .completed (.handle first second) ::
        insideTokens ++
        .residual (dart outer (!outerNegative)) ::
        outsideTokens)
  first_ne_second : first ≠ second
  first_ne_outer : first ≠ outer
  second_ne_outer : second ≠ outer
  first_not_mem_inside :
    first ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  first_not_mem_outside :
    first ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart
  second_not_mem_inside :
    second ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  second_not_mem_outside :
    second ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart
  outer_not_mem_inside :
    outer ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  outer_not_mem_outside :
    outer ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart

namespace MarkedHandleBlockCommute

/-- Exact marked target after moving the completed handle outside the residual pair. -/
def targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens) :
    List (ReductionToken n) :=
  .completed (.handle commute.first
      commute.second) ::
    .residual
      (dart commute.outer commute.outerNegative) ::
    commute.insideTokens ++
    .residual
      (dart commute.outer (!commute.outerNegative)) ::
    commute.outsideTokens

/-- Handle commuting merely permutes atomic marked tokens. -/
theorem perm_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens) :
    tokens.Perm commute.targetTokens := by
  apply commute.rotated.perm.trans
  simpa [targetTokens] using
    (List.Perm.swap
      (.residual
        (dart commute.outer commute.outerNegative))
      (.completed
        (.handle commute.first commute.second))
      (commute.insideTokens ++
        .residual
          (dart commute.outer
            (!commute.outerNegative)) ::
        commute.outsideTokens)).symm

/-- Expansion of the marked source is the generic contextual handle source spelling. -/
theorem expand_isRotated_sourceWord {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens) :
    (ReductionToken.expand tokens).IsRotated
      (HandleBlockCommute.sourceWord
        commute.outer commute.first commute.second
        commute.outerNegative
        (ReductionToken.expand commute.insideTokens)
        (ReductionToken.expand
          commute.outsideTokens)) := by
  have hexpanded :=
    ReductionToken.expand_isRotated commute.rotated
  cases hnegative : commute.outerNegative <;>
    simpa [HandleBlockCommute.sourceWord,
      HandleBlockCommute.positiveSourceWord,
      HandleBlockCommute.negativeSourceWord,
      hnegative, ReductionToken.expand_cons,
      ReductionToken.expand_append,
      ReductionToken.word_residual,
      ReductionToken.word_completed,
      CompletedBlock.word, dart,
      List.append_assoc] using hexpanded

/-- Expansion of the exact marked target is the generic contextual handle target spelling. -/
theorem expand_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens) :
    ReductionToken.expand commute.targetTokens =
      HandleBlockCommute.targetWord
        commute.outer commute.first commute.second
        commute.outerNegative
        (ReductionToken.expand commute.insideTokens)
        (ReductionToken.expand
          commute.outsideTokens) := by
  cases hnegative : commute.outerNegative <;>
    simp [targetTokens, HandleBlockCommute.targetWord,
      HandleBlockCommute.positiveTargetWord,
      HandleBlockCommute.negativeTargetWord,
      hnegative, ReductionToken.expand_cons,
      ReductionToken.expand_append,
      ReductionToken.word_residual,
      ReductionToken.word_completed,
      CompletedBlock.word, dart]

/-- Handle commuting preserves the separated namespace invariant. -/
theorem targetTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ReductionToken.IsSeparated commute.targetTokens :=
  separated.of_perm commute.perm_targetTokens

/-- Handle commuting preserves the classified-token grammar. -/
theorem targetTokens_allClassified {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ReductionToken.AllClassified commute.targetTokens :=
  classified.of_perm commute.perm_targetTokens

/-- Handle commuting preserves unique ownership of protected names. -/
theorem targetTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames
      commute.targetTokens).Nodup :=
  ReductionToken.protectedNames_nodup_of_perm
    nodup commute.perm_targetTokens

end MarkedHandleBlockCommute

/-- Two adjacent extracted boundary singletons which form a P1-subdivided boundary segment. -/
structure MarkedBoundaryPairContraction {n : ℕ}
    (tokens : List (ReductionToken (n + 1))) where
  /-- The `first` declaration. -/
  first : Fin (n + 1)
  /-- The `second` declaration. -/
  second : Fin (n + 1)
  /-- The `firstNegative` declaration. -/
  firstNegative : Bool
  /-- The `secondNegative` declaration. -/
  secondNegative : Bool
  /-- The `tailTokens` declaration. -/
  tailTokens : List (ReductionToken (n + 1))
  rotated :
    tokens.IsRotated
      ([.extracted
          (.boundary first firstNegative),
        .extracted
          (.boundary second secondNegative)] ++
        tailTokens)
  first_ne_second : first ≠ second
  first_not_mem_tail :
    first ∉
      (ReductionToken.expand tailTokens).map edgeOfDart
  second_not_mem_tail :
    second ∉
      (ReductionToken.expand tailTokens).map edgeOfDart

namespace MarkedBoundaryPairContraction

/-- Build a boundary contraction from a displayed adjacent pair.  Separation rules the protected
names out of the residual tail, while duplicate-freeness of protected names supplies distinctness
and rules them out of every protected tail token. -/
def ofRotatedOfProtectedNodup {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (tailTokens : List (ReductionToken (n + 1)))
    (rotated :
      tokens.IsRotated
        ([.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++
          tailTokens))
    (separated : ReductionToken.IsSeparated tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    MarkedBoundaryPairContraction tokens := by
  let displayedTokens :=
    [.extracted (.boundary first firstNegative),
      .extracted (.boundary second secondNegative)] ++
      tailTokens
  have separatedDisplayed :
      ReductionToken.IsSeparated displayedTokens :=
    separated.of_isRotated rotated
  have protectedNodupDisplayed :
      (ReductionToken.protectedNames displayedTokens).Nodup :=
    (ReductionToken.protectedNames_isRotated
      rotated).nodup_iff.mp protectedNodup
  have protectedFacts :
      first ≠ second ∧
        first ∉ ReductionToken.protectedNames tailTokens ∧
        second ∉ ReductionToken.protectedNames tailTokens := by
    have facts :
        (first ≠ second ∧
          first ∉ ReductionToken.protectedNames tailTokens) ∧
        second ∉ ReductionToken.protectedNames tailTokens ∧
          (ReductionToken.protectedNames tailTokens).Nodup := by
      simpa [displayedTokens, ExtractedBlock.edges] using
        protectedNodupDisplayed
    exact ⟨facts.1.1, facts.1.2, facts.2.1⟩
  have not_mem_tail (edge : Fin (n + 1))
      (headProtected :
        edge ∈
          ReductionToken.protectedEdges displayedTokens)
      (tailProtected :
        edge ∉ ReductionToken.protectedNames tailTokens) :
      edge ∉
        (ReductionToken.expand tailTokens).map edgeOfDart := by
    rw [ReductionToken.mem_map_edgeOfDart_expand_iff,
      not_or]
    refine ⟨?_, ?_⟩
    · intro residualTail
      exact (List.disjoint_left.mp separatedDisplayed)
        (by
          change edge ∈
          (ReductionToken.residualDarts
            tailTokens).map edgeOfDart
          exact residualTail)
        headProtected
    · intro hprotected
      apply tailProtected
      exact
        (ReductionToken.mem_protectedNames_iff_mem_protectedEdges
          tailTokens edge).mpr hprotected
  exact
    { first := first
      second := second
      firstNegative := firstNegative
      secondNegative := secondNegative
      tailTokens := tailTokens
      rotated := rotated
      first_ne_second := protectedFacts.1
      first_not_mem_tail :=
        not_mem_tail first
          (by simp [displayedTokens,
            ExtractedBlock.edges])
          protectedFacts.2.1
      second_not_mem_tail :=
        not_mem_tail second
          (by simp [displayedTokens,
            ExtractedBlock.edges])
          protectedFacts.2.2 }

/-- Exact marked target after contracting the second boundary subdivision edge. -/
def targetTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens) :
    List (ReductionToken n) :=
  .extracted
      (.boundary
        (Cancellation.lowerEdge
          contraction.second contraction.first
          contraction.first_ne_second)
        false) ::
    ReductionToken.lowerTokensAvoiding
      contraction.second contraction.tailTokens
      contraction.second_not_mem_tail

/-- Expansion of the marked source is the adjacent-boundary contraction source spelling. -/
theorem expand_isRotated_sourceWord {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens) :
    (ReductionToken.expand tokens).IsRotated
      (BoundaryPairContraction.sourceWord
        contraction.first contraction.second
        contraction.firstNegative
        contraction.secondNegative
        (ReductionToken.expand
          contraction.tailTokens)) := by
  have hexpanded :=
    ReductionToken.expand_isRotated
      contraction.rotated
  simpa [BoundaryPairContraction.sourceWord,
    ReductionToken.expand_cons,
    ReductionToken.expand_append,
    ReductionToken.word_extracted,
    ExtractedBlock.word, List.append_assoc] using
    hexpanded

/-- Expansion of the marked target is the word-level P1 contraction target. -/
theorem expand_targetTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens) :
    ReductionToken.expand contraction.targetTokens =
      BoundaryPairContraction.targetWord
        contraction.first contraction.second
        contraction.first_ne_second
        (ReductionToken.expand
          contraction.tailTokens) := by
  simp [targetTokens,
    BoundaryPairContraction.targetWord,
    ReductionToken.expand_cons,
    ReductionToken.word_extracted,
    ExtractedBlock.word,
    ReductionToken.expand_lowerTokensAvoiding,
    dart]

/-- Boundary-subdivision contraction preserves the classified-token grammar. -/
theorem targetTokens_allClassified {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ReductionToken.AllClassified
      contraction.targetTokens := by
  have displayed :=
    classified.of_isRotated contraction.rotated
  have tailClassified :
      ReductionToken.AllClassified
        contraction.tailTokens := by
    intro token htoken
    exact displayed token (by simp [htoken])
  rw [targetTokens,
    ReductionToken.allClassified_cons]
  exact
    ⟨trivial,
      tailClassified.lowerTokensAvoiding
        contraction.second contraction.tailTokens
        contraction.second_not_mem_tail⟩

/-- Boundary-subdivision contraction preserves separation of residual and protected names. -/
theorem targetTokens_isSeparated {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens)
    (separated : ReductionToken.IsSeparated tokens) :
    ReductionToken.IsSeparated
      contraction.targetTokens := by
  let displayedTokens :=
    [.extracted
        (.boundary contraction.first
          contraction.firstNegative),
      .extracted
        (.boundary contraction.second
          contraction.secondNegative)] ++
      contraction.tailTokens
  have separatedDisplayed :
      ReductionToken.IsSeparated displayedTokens :=
    separated.of_isRotated contraction.rotated
  have tailSeparated :
      ReductionToken.IsSeparated
        contraction.tailTokens := by
    rw [ReductionToken.IsSeparated,
      List.disjoint_left]
    intro edge heResidual heProtected
    have heDisplayedResidual :
        edge ∈
          (ReductionToken.residualDarts
            displayedTokens).map edgeOfDart := by
      change edge ∈
        (ReductionToken.residualDarts
          contraction.tailTokens).map edgeOfDart
      exact heResidual
    have heDisplayedProtected :
        edge ∈
          ReductionToken.protectedEdges
            displayedTokens := by
      change edge ∈
        [contraction.first, contraction.second] ++
          ReductionToken.protectedEdges
            contraction.tailTokens
      exact List.mem_append_right _ heProtected
    exact (List.disjoint_left.mp separatedDisplayed)
      heDisplayedResidual heDisplayedProtected
  let loweredTail :=
    ReductionToken.lowerTokensAvoiding
      contraction.second contraction.tailTokens
      contraction.second_not_mem_tail
  have loweredTailSeparated :
      ReductionToken.IsSeparated loweredTail :=
    tailSeparated.lowerTokensAvoiding
      contraction.second contraction.tailTokens
      contraction.second_not_mem_tail
  rw [ReductionToken.IsSeparated,
    List.disjoint_left]
  intro edge heResidual heProtected
  have heTailResidual :
      edge ∈
        (ReductionToken.residualDarts
          loweredTail).map edgeOfDart := by
    simpa [targetTokens, loweredTail] using heResidual
  have heProtectedCases :
      edge =
          Cancellation.lowerEdge
            contraction.second contraction.first
            contraction.first_ne_second ∨
        edge ∈
          ReductionToken.protectedEdges
            loweredTail := by
    simpa [targetTokens, loweredTail,
      ExtractedBlock.edges] using heProtected
  rcases heProtectedCases with rfl | heTailProtected
  · have hfirstResidual :
        contraction.first ∈
          (ReductionToken.residualDarts
            contraction.tailTokens).map edgeOfDart := by
      rw [←
        ReductionToken.residualEdges_lowerTokensAvoiding_map_restoreEdge
          contraction.second contraction.tailTokens
          contraction.second_not_mem_tail]
      exact List.mem_map.mpr
        ⟨Cancellation.lowerEdge
            contraction.second contraction.first
            contraction.first_ne_second,
          heTailResidual,
          Cancellation.restoreEdge_lowerEdge
            contraction.second contraction.first
            contraction.first_ne_second⟩
    have hfirstDisplayedResidual :
        contraction.first ∈
          (ReductionToken.residualDarts
            displayedTokens).map edgeOfDart := by
      change contraction.first ∈
        (ReductionToken.residualDarts
          contraction.tailTokens).map edgeOfDart
      exact hfirstResidual
    have hfirstDisplayedProtected :
        contraction.first ∈
          ReductionToken.protectedEdges
            displayedTokens := by
      simp [displayedTokens,
        ExtractedBlock.edges]
    exact (List.disjoint_left.mp separatedDisplayed)
      hfirstDisplayedResidual
      hfirstDisplayedProtected
  · exact
      (List.disjoint_left.mp loweredTailSeparated)
        heTailResidual heTailProtected

/-- Boundary-subdivision contraction preserves duplicate-freeness of protected name spines. -/
theorem targetTokens_protectedNames_nodup {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens)
    (nodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (ReductionToken.protectedNames
      contraction.targetTokens).Nodup := by
  let displayedTokens :=
    [.extracted
        (.boundary contraction.first
          contraction.firstNegative),
      .extracted
        (.boundary contraction.second
          contraction.secondNegative)] ++
      contraction.tailTokens
  have displayedNodup :
      (ReductionToken.protectedNames
        displayedTokens).Nodup :=
    (ReductionToken.protectedNames_isRotated
      contraction.rotated).nodup_iff.mp nodup
  have sourceFacts :
      contraction.first ∉
          ReductionToken.protectedNames
            contraction.tailTokens ∧
        (ReductionToken.protectedNames
          contraction.tailTokens).Nodup := by
    have allFacts :
        contraction.first ≠ contraction.second ∧
          contraction.first ∉
            ReductionToken.protectedNames
              contraction.tailTokens ∧
          contraction.second ∉
            ReductionToken.protectedNames
              contraction.tailTokens ∧
          (ReductionToken.protectedNames
            contraction.tailTokens).Nodup := by
      have facts :
          (contraction.first ≠ contraction.second ∧
            contraction.first ∉
              ReductionToken.protectedNames
                contraction.tailTokens) ∧
          contraction.second ∉
              ReductionToken.protectedNames
                contraction.tailTokens ∧
            (ReductionToken.protectedNames
              contraction.tailTokens).Nodup := by
        simpa [displayedTokens,
          ExtractedBlock.edges] using displayedNodup
      exact
        ⟨facts.1.1, facts.1.2,
          facts.2.1, facts.2.2⟩
    exact ⟨allFacts.2.1, allFacts.2.2.2⟩
  let loweredTail :=
    ReductionToken.lowerTokensAvoiding
      contraction.second contraction.tailTokens
      contraction.second_not_mem_tail
  have loweredTailNodup :
      (ReductionToken.protectedNames loweredTail).Nodup :=
    ReductionToken.protectedNames_nodup_lowerTokensAvoiding
      contraction.second contraction.tailTokens
      contraction.second_not_mem_tail sourceFacts.2
  rw [targetTokens]
  simp only [ReductionToken.protectedNames_cons,
    ReductionToken.extractedNames_extracted,
    ExtractedBlock.edges, List.singleton_append,
    List.nodup_cons]
  refine ⟨?_, loweredTailNodup⟩
  intro hlowered
  apply sourceFacts.1
  rw [←
    ReductionToken.protectedNames_lowerTokensAvoiding_map_restoreEdge
      contraction.second contraction.tailTokens
      contraction.second_not_mem_tail]
  exact List.mem_map.mpr
    ⟨Cancellation.lowerEdge
        contraction.second contraction.first
        contraction.first_ne_second,
      hlowered,
      Cancellation.restoreEdge_lowerEdge
      contraction.second contraction.first
        contraction.first_ne_second⟩

/-- Boundary-subdivision contraction preserves the number of residual darts. -/
theorem residualDarts_targetTokens_length_eq {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens) :
    (ReductionToken.residualDarts
      contraction.targetTokens).length =
        (ReductionToken.residualDarts tokens).length := by
  have hsource :=
    (ReductionToken.residualEdges_isRotated
      contraction.rotated).perm.length_eq
  have hsource' :
      (ReductionToken.residualDarts tokens).length =
        (ReductionToken.residualDarts
          contraction.tailTokens).length := by
    simpa using hsource
  have hlower :=
    ReductionToken.residualDarts_length_lowerTokensAvoiding
      contraction.second contraction.tailTokens
      contraction.second_not_mem_tail
  rw [targetTokens]
  simp only [ReductionToken.residualDarts_cons,
    ReductionToken.residualWord_extracted,
    List.nil_append]
  exact hlower.trans hsource'.symm

end MarkedBoundaryPairContraction

namespace MarkedBoundaryBlockCommute

/-- After commuting a completed boundary loop, the same residual pair surrounds exactly the
strictly shorter protected interval. -/
def targetPair {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (commute : MarkedBoundaryBlockCommute tokens)
    (residualInside :
      ReductionToken.residualDarts
        commute.insideTokens = []) :
    MarkedResidualCancellablePair
      commute.targetTokens where
  edge := commute.outer
  negativeFirst := commute.outerNegative
  betweenTokens := commute.insideTokens
  tailTokens :=
    commute.outsideTokens ++
      [.completed
        (.boundary commute.carrier commute.hole
          commute.carrierNegative
          commute.holeNegative)]
  rotated := by
    simpa [targetTokens, List.append_assoc] using
      (List.isRotated_append
        (l :=
          [.completed
            (.boundary commute.carrier commute.hole
              commute.carrierNegative
              commute.holeNegative)])
        (l' :=
          .residual
              (dart commute.outer
                commute.outerNegative) ::
            commute.insideTokens ++
            .residual
              (dart commute.outer
                (!commute.outerNegative)) ::
            commute.outsideTokens))
  residual_between := residualInside

end MarkedBoundaryBlockCommute

namespace MarkedCrosscapBlockCommute

/-- After contextual crosscap commuting, the old crosscap carrier is the new residual carrier
around exactly the strict tail of the protected interval. -/
def targetPair {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (commute : MarkedCrosscapBlockCommute tokens)
    (residualInside :
      ReductionToken.residualDarts
        commute.insideTokens = []) :
    MarkedResidualCancellablePair
      commute.targetTokens where
  edge := commute.carrier
  negativeFirst := !commute.carrierNegative
  betweenTokens := commute.insideTokens
  tailTokens :=
    ReductionToken.inverseSequence
        commute.outsideTokens ++
      [.completed
        (.crosscap commute.outer
          commute.outerNegative)]
  rotated := by
    simpa [targetTokens, List.append_assoc] using
      (List.isRotated_append
        (l :=
          [.completed
            (.crosscap commute.outer
              commute.outerNegative)])
        (l' :=
          .residual
              (dart commute.carrier
                (!commute.carrierNegative)) ::
            commute.insideTokens ++
            .residual
              (dart commute.carrier
                commute.carrierNegative) ::
            ReductionToken.inverseSequence
              commute.outsideTokens))
  residual_between := residualInside

end MarkedCrosscapBlockCommute

namespace MarkedHandleBlockCommute

/-- After commuting a completed handle, the same residual pair surrounds exactly the strict tail
of the protected interval. -/
def targetPair {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (commute : MarkedHandleBlockCommute tokens)
    (residualInside :
      ReductionToken.residualDarts
        commute.insideTokens = []) :
    MarkedResidualCancellablePair
      commute.targetTokens where
  edge := commute.outer
  negativeFirst := commute.outerNegative
  betweenTokens := commute.insideTokens
  tailTokens :=
    commute.outsideTokens ++
      [.completed
        (.handle commute.first commute.second)]
  rotated := by
    simpa [targetTokens, List.append_assoc] using
      (List.isRotated_append
        (l :=
          [.completed
            (.handle commute.first commute.second)])
        (l' :=
          .residual
              (dart commute.outer
                commute.outerNegative) ::
            commute.insideTokens ++
            .residual
              (dart commute.outer
                (!commute.outerNegative)) ::
            commute.outsideTokens))
  residual_between := residualInside

end MarkedHandleBlockCommute

namespace MarkedResidualCancellablePair

/-- Under the classified-state invariant, the interval crossed by a lifted residual cancellation
is an exact finite list of typed protected atoms. -/
theorem exists_betweenAtoms {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ∃ atoms : List (ProtectedAtom (n + 1)),
      pair.betweenTokens =
        atoms.map ReductionToken.ofProtectedAtom := by
  have displayed :=
    classified.of_isRotated pair.rotated
  have betweenClassified :
      ReductionToken.AllClassified pair.betweenTokens := by
    intro token htoken
    exact displayed token (by simp [htoken])
  exact
    ReductionToken.exists_eq_map_ofProtectedAtom_of_allClassified_of_residualDarts_eq_nil
      pair.betweenTokens betweenClassified
      pair.residual_between

/-- A raw boundary atom with a nonempty protected suffix exposes the Dyck transition which moves
that raw atom behind the suffix. -/
noncomputable def toBoundaryAtomRotateOfValid {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (hole : Fin (n + 1)) (holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .extracted (.boundary hole holeNegative) ::
          insideTokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedBoundaryAtomRotate tokens := by
  have hfresh :=
    pair.edge_not_mem_between_and_tail valid
  have hcarrierHole : pair.edge ≠ hole := by
    intro heq
    apply hfresh.1
    rw [hbetween]
    simp [heq, ExtractedBlock.word]
  have hcarrierInside :
      pair.edge ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart := by
    intro hmem
    apply hfresh.1
    rw [hbetween]
    simp [hmem]
  have hresidualInside :
      ReductionToken.residualDarts insideTokens = [] := by
    have h := pair.residual_between
    rw [hbetween] at h
    simpa using h
  exact
    { carrier := pair.edge
      hole := hole
      carrierNegative := pair.negativeFirst
      holeNegative := holeNegative
      insideTokens := insideTokens
      outsideTokens := pair.tailTokens
      rotated := by
        simpa [hbetween] using pair.rotated
      residual_inside := hresidualInside
      carrier_ne_hole := hcarrierHole
      carrier_not_mem_inside := hcarrierInside
      carrier_not_mem_outside := hfresh.2 }

private theorem toBoundaryAtomRotateOfValid_carrier {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (hole : Fin (n + 1)) (holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween : pair.betweenTokens =
      .extracted (.boundary hole holeNegative) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    (pair.toBoundaryAtomRotateOfValid hole holeNegative insideTokens hbetween valid).carrier =
      pair.edge := by
  rfl

/-- Two raw boundary atoms at the head of a protected residual-pair interval expose an adjacent
P1 contraction after one cyclic token rotation. -/
def toBoundaryPairContraction {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++
          insideTokens)
    (separated : ReductionToken.IsSeparated tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    MarkedBoundaryPairContraction tokens := by
  let contractionTail :=
    insideTokens ++
      .residual
          (dart pair.edge (!pair.negativeFirst)) ::
        pair.tailTokens ++
          [.residual
            (dart pair.edge pair.negativeFirst)]
  have hrotated :
      tokens.IsRotated
        ([.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++
          contractionTail) := by
    apply pair.rotated.trans
    rw [hbetween]
    have hcycle :=
      List.isRotated_append
        (l :=
          [.residual
            (dart pair.edge pair.negativeFirst)])
        (l' :=
          [.extracted (.boundary first firstNegative),
            .extracted (.boundary second secondNegative)] ++
            insideTokens ++
              .residual
                  (dart pair.edge (!pair.negativeFirst)) ::
                pair.tailTokens)
    simpa [contractionTail,
      List.append_assoc] using hcycle
  exact
    MarkedBoundaryPairContraction.ofRotatedOfProtectedNodup
      first second firstNegative secondNegative
      contractionTail hrotated separated protectedNodup

/-- After contracting the first two raw boundary atoms, the same residual inverse pair surrounds
their merged singleton followed by the strict tail of the old protected interval. -/
noncomputable def boundaryContractionTargetPair {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++
          insideTokens)
    (separated : ReductionToken.IsSeparated tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    MarkedResidualCancellablePair
      (pair.toBoundaryPairContraction first second
        firstNegative secondNegative insideTokens hbetween
        separated protectedNodup).targetTokens := by
  let step :=
    pair.toBoundaryPairContraction first second
      firstNegative secondNegative insideTokens hbetween
      separated protectedNodup
  have hsecondInside :
      second ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart := by
    intro hmem
    apply step.second_not_mem_tail
    change second ∈
      (ReductionToken.expand
        (insideTokens ++
          .residual
              (dart pair.edge (!pair.negativeFirst)) ::
            pair.tailTokens ++
              [.residual
                (dart pair.edge pair.negativeFirst)])).map
        edgeOfDart
    simp [hmem]
  have hsecondOutside :
      second ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart := by
    intro hmem
    apply step.second_not_mem_tail
    change second ∈
      (ReductionToken.expand
        (insideTokens ++
          .residual
              (dart pair.edge (!pair.negativeFirst)) ::
            pair.tailTokens ++
              [.residual
                (dart pair.edge pair.negativeFirst)])).map
        edgeOfDart
    simp [hmem]
  have houterSecond : pair.edge ≠ second := by
    intro heq
    apply step.second_not_mem_tail
    change second ∈
      (ReductionToken.expand
        (insideTokens ++
          .residual
              (dart pair.edge (!pair.negativeFirst)) ::
            pair.tailTokens ++
              [.residual
                (dart pair.edge pair.negativeFirst)])).map
        edgeOfDart
    simp [heq]
  let loweredInside :=
    ReductionToken.lowerTokensAvoiding
      second insideTokens hsecondInside
  let loweredOutside :=
    ReductionToken.lowerTokensAvoiding
      second pair.tailTokens hsecondOutside
  let loweredOuter :=
    Cancellation.lowerEdge second pair.edge
      houterSecond
  refine
    { edge := loweredOuter
      negativeFirst := pair.negativeFirst
      betweenTokens :=
        .extracted
            (.boundary
              (Cancellation.lowerEdge second first
                step.first_ne_second)
              false) ::
          loweredInside
      tailTokens := loweredOutside
      rotated := ?_
      residual_between := ?_ }
  · have hcycle :=
      List.isRotated_append
        (l :=
          [.extracted
              (.boundary
                (Cancellation.lowerEdge second first
                  step.first_ne_second)
                false)] ++
            loweredInside ++
              .residual
                  (dart loweredOuter
                    (!pair.negativeFirst)) ::
                loweredOutside)
        (l' :=
          [.residual
            (dart loweredOuter pair.negativeFirst)])
    change step.targetTokens.IsRotated _
    simpa [step, toBoundaryPairContraction,
      MarkedBoundaryPairContraction.ofRotatedOfProtectedNodup,
      MarkedBoundaryPairContraction.targetTokens,
      ReductionToken.lowerTokensAvoiding_append,
      ReductionToken.lowerTokensAvoiding,
      ReductionToken.lowerAvoiding_residual_dart,
      loweredInside, loweredOutside, loweredOuter,
      List.append_assoc] using hcycle
  · have hinsideResidual :
        ReductionToken.residualDarts insideTokens = [] := by
      have h := pair.residual_between
      rw [hbetween] at h
      simpa using h
    have hlowered :=
      ReductionToken.residualEdges_lowerTokensAvoiding_map_restoreEdge
        second insideTokens hsecondInside
    change ReductionToken.residualDarts loweredInside = []
    simpa [loweredInside, hinsideResidual] using hlowered

/-- A boundary contraction removes one protected atom from the selected residual-pair interval. -/
theorem boundaryContractionTargetPair_between_length_lt {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++
          insideTokens)
    (separated : ReductionToken.IsSeparated tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup) :
    (pair.boundaryContractionTargetPair first second
        firstNegative secondNegative insideTokens hbetween
        separated protectedNodup).betweenTokens.length <
      pair.betweenTokens.length := by
  rw [hbetween]
  simp [boundaryContractionTargetPair]

/-- A lifted residual pair surrounding exactly one boundary singleton is a boundary closure. -/
def toBoundaryClosure {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (hole : Fin (n + 1)) (holeNegative : Bool)
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary hole holeNegative)]) :
    MarkedBoundaryClosure tokens where
  carrier := pair.edge
  hole := hole
  carrierNegative := pair.negativeFirst
  holeNegative := holeNegative
  tailTokens := pair.tailTokens
  rotated := by
    simpa [hbetween] using pair.rotated

/-- A lifted residual pair whose protected interval begins with a completed boundary loop exposes
the exact boundary-block commute transition. -/
def toBoundaryBlockCommute {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier hole : Fin (n + 1))
    (carrierNegative holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.boundary carrier hole
          carrierNegative holeNegative) ::
        insideTokens)
    (hcarrierHole : carrier ≠ hole)
    (hcarrierOuter : carrier ≠ pair.edge)
    (hcarrierInside :
      carrier ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart)
    (hcarrierOutside :
      carrier ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart) :
    MarkedBoundaryBlockCommute tokens where
  outer := pair.edge
  carrier := carrier
  hole := hole
  outerNegative := pair.negativeFirst
  carrierNegative := carrierNegative
  holeNegative := holeNegative
  insideTokens := insideTokens
  outsideTokens := pair.tailTokens
  rotated := by
    simpa [hbetween] using pair.rotated
  carrier_ne_hole := hcarrierHole
  carrier_ne_outer := hcarrierOuter
  carrier_not_mem_inside := hcarrierInside
  carrier_not_mem_outside := hcarrierOutside

private theorem not_mem_inside_and_outside_of_count_eq_two {n : ℕ}
    (edge : Fin n) (displayed inside outside : List (Fin n))
    (hcount : displayed.count edge = 2)
    (hsum : displayed.count edge = 2 + inside.count edge + outside.count edge) :
    edge ∉ inside ∧ edge ∉ outside := by
  constructor
  · intro hmem
    have hpositive : 0 < inside.count edge := List.count_pos_iff.mpr hmem
    omega
  · intro hmem
    have hpositive : 0 < outside.count edge := List.count_pos_iff.mpr hmem
    omega

private structure BoundaryBlockCommuteConditions {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier hole : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1))) : Prop where
  carrier_ne_hole : carrier ≠ hole
  carrier_ne_outer : carrier ≠ pair.edge
  carrier_not_mem_inside :
    carrier ∉ (ReductionToken.expand insideTokens).map edgeOfDart
  carrier_not_mem_outside :
    carrier ∉ (ReductionToken.expand pair.tailTokens).map edgeOfDart

private theorem boundaryBlockCommuteConditions_of_valid {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier hole : Fin (n + 1))
    (carrierNegative holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.boundary carrier hole carrierNegative holeNegative) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    BoundaryBlockCommuteConditions pair carrier hole insideTokens := by
  let displayed :=
    dart pair.edge pair.negativeFirst ::
      (CompletedBlock.boundary carrier hole carrierNegative holeNegative).word ++
      ReductionToken.expand insideTokens ++
      dart pair.edge (!pair.negativeFirst) :: ReductionToken.expand pair.tailTokens
  have hexpanded : (ReductionToken.expand tokens).IsRotated displayed := by
    have h := ReductionToken.expand_isRotated pair.rotated
    rw [hbetween] at h
    simpa [displayed, ReductionToken.expand_cons, ReductionToken.expand_append,
      ReductionToken.word_residual, ReductionToken.word_completed, List.append_assoc] using h
  have hmultiplicity := valid.2.2.2 carrier
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  have hpermuted := (hexpanded.map edgeOfDart).perm.count_eq carrier
  have hcount : (displayed.map edgeOfDart).count carrier = 2 := by
    have hlower : 2 ≤ (displayed.map edgeOfDart).count carrier := by
      simp [displayed, CompletedBlock.word, boundaryLoopWord, List.count_cons]
      omega
    omega
  have hcarrierHole : carrier ≠ hole := by
    intro heq
    subst hole
    simp [displayed, CompletedBlock.word, boundaryLoopWord, List.count_cons] at hcount
    omega
  have hcarrierOuter : carrier ≠ pair.edge := by
    intro heq
    subst carrier
    simp [displayed, CompletedBlock.word, boundaryLoopWord, List.count_cons] at hcount
  have hsum :
      (displayed.map edgeOfDart).count carrier =
        2 + ((ReductionToken.expand insideTokens).map edgeOfDart).count carrier +
          ((ReductionToken.expand pair.tailTokens).map edgeOfDart).count carrier := by
    simp [displayed, CompletedBlock.word, boundaryLoopWord, hcarrierHole.symm,
      hcarrierOuter.symm]
    omega
  have hfresh := not_mem_inside_and_outside_of_count_eq_two carrier
    (displayed.map edgeOfDart) ((ReductionToken.expand insideTokens).map edgeOfDart)
    ((ReductionToken.expand pair.tailTokens).map edgeOfDart) hcount hsum
  exact ⟨hcarrierHole, hcarrierOuter, hfresh.1, hfresh.2⟩

/-- Surface multiplicity supplies all freshness conditions needed to commute a completed
boundary-loop atom at the head of a lifted residual-pair interval. -/
noncomputable def toBoundaryBlockCommuteOfValid {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier hole : Fin (n + 1))
    (carrierNegative holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.boundary carrier hole
          carrierNegative holeNegative) ::
        insideTokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedBoundaryBlockCommute tokens := by
  let conditions := boundaryBlockCommuteConditions_of_valid pair carrier hole carrierNegative
    holeNegative insideTokens hbetween valid
  exact pair.toBoundaryBlockCommute carrier hole carrierNegative holeNegative insideTokens hbetween
    conditions.carrier_ne_hole conditions.carrier_ne_outer conditions.carrier_not_mem_inside
    conditions.carrier_not_mem_outside

@[simp]
private theorem toBoundaryBlockCommuteOfValid_insideTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier hole : Fin (n + 1)) (carrierNegative holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.boundary carrier hole carrierNegative holeNegative) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    (pair.toBoundaryBlockCommuteOfValid carrier hole carrierNegative holeNegative insideTokens
      hbetween valid).insideTokens = insideTokens := rfl

@[simp]
private theorem toBoundaryBlockCommuteOfValid_outsideTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier hole : Fin (n + 1)) (carrierNegative holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.boundary carrier hole carrierNegative holeNegative) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    (pair.toBoundaryBlockCommuteOfValid carrier hole carrierNegative holeNegative insideTokens
      hbetween valid).outsideTokens = pair.tailTokens := rfl

/-- A lifted residual pair whose protected interval begins with a completed crosscap exposes the
exact contextual crosscap transition. -/
def toCrosscapBlockCommute {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier : Fin (n + 1))
    (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.crosscap carrier
          carrierNegative) ::
        insideTokens)
    (hcarrierOuter : carrier ≠ pair.edge)
    (hcarrierInside :
      carrier ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart)
    (hcarrierOutside :
      carrier ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart)
    (houterInside :
      pair.edge ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart)
    (houterOutside :
      pair.edge ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart) :
    MarkedCrosscapBlockCommute tokens where
  outer := pair.edge
  carrier := carrier
  outerNegative := pair.negativeFirst
  carrierNegative := carrierNegative
  insideTokens := insideTokens
  outsideTokens := pair.tailTokens
  rotated := by
    simpa [hbetween] using pair.rotated
  carrier_ne_outer := hcarrierOuter
  carrier_not_mem_inside := hcarrierInside
  carrier_not_mem_outside := hcarrierOutside
  outer_not_mem_inside := houterInside
  outer_not_mem_outside := houterOutside

private structure CrosscapBlockCommuteConditions {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1))) : Prop where
  carrier_ne_outer : carrier ≠ pair.edge
  carrier_not_mem_inside :
    carrier ∉ (ReductionToken.expand insideTokens).map edgeOfDart
  carrier_not_mem_outside :
    carrier ∉ (ReductionToken.expand pair.tailTokens).map edgeOfDart
  outer_not_mem_inside :
    pair.edge ∉ (ReductionToken.expand insideTokens).map edgeOfDart
  outer_not_mem_outside :
    pair.edge ∉ (ReductionToken.expand pair.tailTokens).map edgeOfDart

private theorem crosscapBlockCommuteConditions_of_valid {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier : Fin (n + 1)) (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens = .completed (.crosscap carrier carrierNegative) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    CrosscapBlockCommuteConditions pair carrier insideTokens := by
  let displayed :=
    dart pair.edge pair.negativeFirst ::
      (CompletedBlock.crosscap carrier carrierNegative).word ++
      ReductionToken.expand insideTokens ++
      dart pair.edge (!pair.negativeFirst) :: ReductionToken.expand pair.tailTokens
  have hexpanded : (ReductionToken.expand tokens).IsRotated displayed := by
    have h := ReductionToken.expand_isRotated pair.rotated
    rw [hbetween] at h
    simpa [displayed, ReductionToken.expand_cons, ReductionToken.expand_append,
      ReductionToken.word_residual, ReductionToken.word_completed, List.append_assoc] using h
  have hvalidCount (edge : Fin (n + 1)) :
      (displayed.map edgeOfDart).count edge = 1 ∨
        (displayed.map edgeOfDart).count edge = 2 := by
    have hmultiplicity := valid.2.2.2 edge
    rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
    have hpermuted := (hexpanded.map edgeOfDart).perm.count_eq edge
    omega
  have hcarrierCount : (displayed.map edgeOfDart).count carrier = 2 := by
    have h := hvalidCount carrier
    have hlower : 2 ≤ (displayed.map edgeOfDart).count carrier := by
      simp [displayed, CompletedBlock.word, List.count_cons]
      omega
    omega
  have houterCount : (displayed.map edgeOfDart).count pair.edge = 2 := by
    have h := hvalidCount pair.edge
    have hlower : 2 ≤ (displayed.map edgeOfDart).count pair.edge := by
      simp [displayed, CompletedBlock.word, List.count_cons]
      omega
    omega
  have hcarrierOuter : carrier ≠ pair.edge := by
    intro heq
    subst carrier
    simp [displayed, CompletedBlock.word] at houterCount
  have hcarrierSum :
      (displayed.map edgeOfDart).count carrier =
        2 + ((ReductionToken.expand insideTokens).map edgeOfDart).count carrier +
          ((ReductionToken.expand pair.tailTokens).map edgeOfDart).count carrier := by
    simp [displayed, CompletedBlock.word, hcarrierOuter.symm]
    omega
  have houterSum :
      (displayed.map edgeOfDart).count pair.edge =
        2 + ((ReductionToken.expand insideTokens).map edgeOfDart).count pair.edge +
          ((ReductionToken.expand pair.tailTokens).map edgeOfDart).count pair.edge := by
    simp [displayed, CompletedBlock.word, hcarrierOuter]
    omega
  have hcarrierFresh := not_mem_inside_and_outside_of_count_eq_two carrier
    (displayed.map edgeOfDart) ((ReductionToken.expand insideTokens).map edgeOfDart)
    ((ReductionToken.expand pair.tailTokens).map edgeOfDart) hcarrierCount hcarrierSum
  have houterFresh := not_mem_inside_and_outside_of_count_eq_two pair.edge
    (displayed.map edgeOfDart) ((ReductionToken.expand insideTokens).map edgeOfDart)
    ((ReductionToken.expand pair.tailTokens).map edgeOfDart) houterCount houterSum
  exact ⟨hcarrierOuter, hcarrierFresh.1, hcarrierFresh.2, houterFresh.1, houterFresh.2⟩

/-- Surface multiplicity supplies every freshness condition needed for a contextual crosscap
transition at the head of a lifted residual-pair interval. -/
noncomputable def toCrosscapBlockCommuteOfValid {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier : Fin (n + 1))
    (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.crosscap carrier
          carrierNegative) ::
        insideTokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedCrosscapBlockCommute tokens := by
  let conditions := crosscapBlockCommuteConditions_of_valid pair carrier carrierNegative
    insideTokens hbetween valid
  exact pair.toCrosscapBlockCommute carrier carrierNegative insideTokens hbetween
    conditions.carrier_ne_outer conditions.carrier_not_mem_inside
    conditions.carrier_not_mem_outside conditions.outer_not_mem_inside
    conditions.outer_not_mem_outside

@[simp]
private theorem toCrosscapBlockCommuteOfValid_insideTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier : Fin (n + 1)) (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens = .completed (.crosscap carrier carrierNegative) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    (pair.toCrosscapBlockCommuteOfValid carrier carrierNegative insideTokens hbetween valid
      ).insideTokens = insideTokens := rfl

@[simp]
private theorem toCrosscapBlockCommuteOfValid_outsideTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (carrier : Fin (n + 1)) (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens = .completed (.crosscap carrier carrierNegative) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    (pair.toCrosscapBlockCommuteOfValid carrier carrierNegative insideTokens hbetween valid
      ).outsideTokens = pair.tailTokens := rfl

/-- A lifted residual pair whose protected interval begins with a completed handle exposes the
exact contextual handle transition. -/
def toHandleBlockCommute {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.handle first second) ::
        insideTokens)
    (hfirstSecond : first ≠ second)
    (hfirstOuter : first ≠ pair.edge)
    (hsecondOuter : second ≠ pair.edge)
    (hfirstInside :
      first ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart)
    (hfirstOutside :
      first ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart)
    (hsecondInside :
      second ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart)
    (hsecondOutside :
      second ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart)
    (houterInside :
      pair.edge ∉
        (ReductionToken.expand insideTokens).map
          edgeOfDart)
    (houterOutside :
      pair.edge ∉
        (ReductionToken.expand pair.tailTokens).map
          edgeOfDart) :
    MarkedHandleBlockCommute tokens where
  outer := pair.edge
  first := first
  second := second
  outerNegative := pair.negativeFirst
  insideTokens := insideTokens
  outsideTokens := pair.tailTokens
  rotated := by
    simpa [hbetween] using pair.rotated
  first_ne_second := hfirstSecond
  first_ne_outer := hfirstOuter
  second_ne_outer := hsecondOuter
  first_not_mem_inside := hfirstInside
  first_not_mem_outside := hfirstOutside
  second_not_mem_inside := hsecondInside
  second_not_mem_outside := hsecondOutside
  outer_not_mem_inside := houterInside
  outer_not_mem_outside := houterOutside

private structure HandleBlockCommuteConditions {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1))) : Prop where
  first_ne_second : first ≠ second
  first_ne_outer : first ≠ pair.edge
  second_ne_outer : second ≠ pair.edge
  first_not_mem_inside : first ∉ (ReductionToken.expand insideTokens).map edgeOfDart
  first_not_mem_outside : first ∉ (ReductionToken.expand pair.tailTokens).map edgeOfDart
  second_not_mem_inside : second ∉ (ReductionToken.expand insideTokens).map edgeOfDart
  second_not_mem_outside : second ∉ (ReductionToken.expand pair.tailTokens).map edgeOfDart
  outer_not_mem_inside : pair.edge ∉ (ReductionToken.expand insideTokens).map edgeOfDart
  outer_not_mem_outside : pair.edge ∉ (ReductionToken.expand pair.tailTokens).map edgeOfDart

private theorem handleBlockCommuteConditions_of_valid {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween : pair.betweenTokens = .completed (.handle first second) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    HandleBlockCommuteConditions pair first second insideTokens := by
  let displayed :=
    dart pair.edge pair.negativeFirst ::
      (CompletedBlock.handle first second).word ++ ReductionToken.expand insideTokens ++
      dart pair.edge (!pair.negativeFirst) :: ReductionToken.expand pair.tailTokens
  have hexpanded : (ReductionToken.expand tokens).IsRotated displayed := by
    have h := ReductionToken.expand_isRotated pair.rotated
    rw [hbetween] at h
    simpa [displayed, ReductionToken.expand_cons, ReductionToken.expand_append,
      ReductionToken.word_residual, ReductionToken.word_completed, List.append_assoc] using h
  have hvalidCount (edge : Fin (n + 1)) :
      (displayed.map edgeOfDart).count edge = 1 ∨
        (displayed.map edgeOfDart).count edge = 2 := by
    have hmultiplicity := valid.2.2.2 edge
    rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
    have hpermuted := (hexpanded.map edgeOfDart).perm.count_eq edge
    omega
  have hfirstCount : (displayed.map edgeOfDart).count first = 2 := by
    have h := hvalidCount first
    have hlower : 2 ≤ (displayed.map edgeOfDart).count first := by
      simp [displayed, CompletedBlock.word, List.count_cons]
      omega
    omega
  have hsecondCount : (displayed.map edgeOfDart).count second = 2 := by
    have h := hvalidCount second
    have hlower : 2 ≤ (displayed.map edgeOfDart).count second := by
      simp [displayed, CompletedBlock.word, List.count_cons]
      omega
    omega
  have houterCount : (displayed.map edgeOfDart).count pair.edge = 2 := by
    have h := hvalidCount pair.edge
    have hlower : 2 ≤ (displayed.map edgeOfDart).count pair.edge := by
      simp [displayed, CompletedBlock.word, List.count_cons]
      omega
    omega
  have hfirstSecond : first ≠ second := by
    intro heq
    subst second
    simp [displayed, CompletedBlock.word, List.count_cons] at hfirstCount
    omega
  have hfirstOuter : first ≠ pair.edge := by
    intro heq
    subst first
    simp [displayed, CompletedBlock.word, hfirstSecond.symm] at houterCount
  have hsecondOuter : second ≠ pair.edge := by
    intro heq
    subst second
    simp [displayed, CompletedBlock.word, hfirstSecond] at houterCount
  have hfirstSum :
      (displayed.map edgeOfDart).count first =
        2 + ((ReductionToken.expand insideTokens).map edgeOfDart).count first +
          ((ReductionToken.expand pair.tailTokens).map edgeOfDart).count first := by
    simp [displayed, CompletedBlock.word, hfirstSecond.symm, hfirstOuter.symm]
    omega
  have hsecondSum :
      (displayed.map edgeOfDart).count second =
        2 + ((ReductionToken.expand insideTokens).map edgeOfDart).count second +
          ((ReductionToken.expand pair.tailTokens).map edgeOfDart).count second := by
    simp [displayed, CompletedBlock.word, hfirstSecond, hsecondOuter.symm]
    omega
  have houterSum :
      (displayed.map edgeOfDart).count pair.edge =
        2 + ((ReductionToken.expand insideTokens).map edgeOfDart).count pair.edge +
          ((ReductionToken.expand pair.tailTokens).map edgeOfDart).count pair.edge := by
    simp [displayed, CompletedBlock.word, hfirstOuter, hsecondOuter]
    omega
  have hfirstFresh := not_mem_inside_and_outside_of_count_eq_two first
    (displayed.map edgeOfDart) ((ReductionToken.expand insideTokens).map edgeOfDart)
    ((ReductionToken.expand pair.tailTokens).map edgeOfDart) hfirstCount hfirstSum
  have hsecondFresh := not_mem_inside_and_outside_of_count_eq_two second
    (displayed.map edgeOfDart) ((ReductionToken.expand insideTokens).map edgeOfDart)
    ((ReductionToken.expand pair.tailTokens).map edgeOfDart) hsecondCount hsecondSum
  have houterFresh := not_mem_inside_and_outside_of_count_eq_two pair.edge
    (displayed.map edgeOfDart) ((ReductionToken.expand insideTokens).map edgeOfDart)
    ((ReductionToken.expand pair.tailTokens).map edgeOfDart) houterCount houterSum
  exact ⟨hfirstSecond, hfirstOuter, hsecondOuter, hfirstFresh.1, hfirstFresh.2,
    hsecondFresh.1, hsecondFresh.2, houterFresh.1, houterFresh.2⟩

/-- Surface multiplicity supplies every distinction and freshness condition needed for a
contextual handle transition. -/
noncomputable def toHandleBlockCommuteOfValid {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.handle first second) ::
        insideTokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedHandleBlockCommute tokens := by
  let conditions :=
    handleBlockCommuteConditions_of_valid pair first second insideTokens hbetween valid
  exact pair.toHandleBlockCommute first second insideTokens hbetween conditions.first_ne_second
    conditions.first_ne_outer conditions.second_ne_outer conditions.first_not_mem_inside
    conditions.first_not_mem_outside conditions.second_not_mem_inside
    conditions.second_not_mem_outside conditions.outer_not_mem_inside
    conditions.outer_not_mem_outside

@[simp]
private theorem toHandleBlockCommuteOfValid_insideTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween : pair.betweenTokens = .completed (.handle first second) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    (pair.toHandleBlockCommuteOfValid first second insideTokens hbetween valid).insideTokens =
      insideTokens := rfl

@[simp]
private theorem toHandleBlockCommuteOfValid_outsideTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween : pair.betweenTokens = .completed (.handle first second) :: insideTokens)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    (pair.toHandleBlockCommuteOfValid first second insideTokens hbetween valid).outsideTokens =
      pair.tailTokens := rfl

/-- Exhaustive local disposition of a lifted residual inverse pair.  The first two constructors
are already executable.  The final constructor isolates the remaining contextual move: commuting
a nontrivial protected interval out of the inverse pair before cancellation. -/
inductive Disposition {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens) : Type
  | adjacent
      (between_eq : pair.betweenTokens = []) :
      Disposition pair
  | boundary
      (hole : Fin (n + 1)) (holeNegative : Bool)
      (between_eq :
        pair.betweenTokens =
          [.extracted (.boundary hole holeNegative)]) :
      Disposition pair
  | contextual
      (between_ne : pair.betweenTokens ≠ [])
      (not_boundary :
        ∀ (hole : Fin (n + 1)) (holeNegative : Bool),
          pair.betweenTokens ≠
            [.extracted (.boundary hole holeNegative)]) :
      Disposition pair

/-- Classify every lifted residual pair into the two completed executable cases or the exact
remaining contextual case. -/
noncomputable def disposition {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens) :
    Disposition pair := by
  by_cases hempty : pair.betweenTokens = []
  · exact .adjacent hempty
  · by_cases hboundary :
      ∃ (hole : Fin (n + 1)) (holeNegative : Bool),
        pair.betweenTokens =
          [.extracted (.boundary hole holeNegative)]
    · let hole := Classical.choose hboundary
      let orientationWitness := Classical.choose_spec hboundary
      let holeNegative := Classical.choose orientationWitness
      exact .boundary hole holeNegative
        (Classical.choose_spec orientationWitness)
    · exact .contextual hempty (by
        intro hole holeNegative hbetween
        exact hboundary ⟨hole, holeNegative, hbetween⟩)

/-- Classified-state refinement of `Disposition`: every genuinely contextual interval exposes
its first typed protected atom and the exact remaining atom list. -/
inductive ClassifiedDisposition {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens) : Type
  | adjacent
      (between_eq : pair.betweenTokens = []) :
      ClassifiedDisposition pair
  | boundary
      (hole : Fin (n + 1)) (holeNegative : Bool)
      (between_eq :
        pair.betweenTokens =
          [.extracted (.boundary hole holeNegative)]) :
      ClassifiedDisposition pair
  | structured
      (first : ProtectedAtom (n + 1))
      (rest : List (ProtectedAtom (n + 1)))
      (between_eq :
        pair.betweenTokens =
          (first :: rest).map
            ReductionToken.ofProtectedAtom) :
      ClassifiedDisposition pair

/-- Exhaustively expose the typed protected interval of a lifted residual pair.  A singleton raw
boundary atom is kept as the dedicated executable boundary-closure case. -/
noncomputable def classifiedDisposition {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (classified : ReductionToken.AllClassified tokens) :
    ClassifiedDisposition pair := by
  let witness := pair.exists_betweenAtoms classified
  have hatoms := Classical.choose_spec witness
  cases hatomsList : Classical.choose witness with
  | nil =>
      rw [hatomsList] at hatoms
      exact .adjacent (by simpa using hatoms)
  | cons first rest =>
      rw [hatomsList] at hatoms
      cases first with
      | boundary hole holeNegative =>
          cases rest with
          | nil =>
              exact .boundary hole holeNegative
                (by simpa [ReductionToken.ofProtectedAtom] using hatoms)
          | cons second rest =>
              exact .structured
                (.boundary hole holeNegative)
                (second :: rest) hatoms
      | completed block =>
          exact .structured (.completed block) rest hatoms

end MarkedResidualCancellablePair

/-- A complete proof-relevant decomposition trace.  Each step extracts one certified block, then
pair-reduces the strictly shorter residual before continuing. -/
inductive ResidualDecomposition {n : ℕ} :
    List (SignedDart (Fin n)) → Type
  | done : ResidualDecomposition []
  | step {word : List (SignedDart (Fin n))}
      (feature : ActionablePairReductionFeature word)
      (reduction : ResidualPairReduction feature.residualWord)
      (tail : ResidualDecomposition reduction.reducedWord) :
      ResidualDecomposition word

namespace ResidualDecomposition

/-- Extracted blocks, in recursive extraction order. -/
def blocks {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → List (ExtractedBlock n)
  | .done => []
  | .step feature _ tail => feature.block :: tail.blocks

/-- Edge names consumed by all blocks in extraction order. -/
def extractedEdges {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → List (Fin n)
  | .done => []
  | .step feature _ tail =>
      feature.extractedEdges ++ tail.extractedEdges

/-- Number of boundary singleton blocks in a decomposition. -/
def boundaryCount {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → ℕ
  | .done => 0
  | .step feature _ tail =>
      (match feature.block with
        | .boundary _ _ => 1
        | _ => 0) + tail.boundaryCount

/-- Number of crosscap square blocks in a decomposition. -/
def crosscapCount {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → ℕ
  | .done => 0
  | .step feature _ tail =>
      (match feature.block with
        | .crosscap _ _ => 1
        | _ => 0) + tail.crosscapCount

/-- Number of handle blocks in a decomposition. -/
def handleCount {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → ℕ
  | .done => 0
  | .step feature _ tail =>
      (match feature.block with
        | .handle _ _ => 1
        | _ => 0) + tail.handleCount

/-- The normal-form parameters selected by a complete block decomposition.  In the presence of
any crosscap, each handle contributes two additional crosscaps via Gallier--Xu Step 5. -/
def normalForm {n : ℕ} {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word) : NormalForm :=
  if decomposition.crosscapCount = 0 then
    .orientable decomposition.handleCount
      decomposition.boundaryCount
  else
    .nonOrientable
      (decomposition.crosscapCount +
        2 * decomposition.handleCount)
      decomposition.boundaryCount

/-- Every extracted block belongs to exactly one of the three block classes. -/
theorem count_sum_eq_blocks_length {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word) :
    decomposition.boundaryCount +
        decomposition.crosscapCount +
        decomposition.handleCount =
      decomposition.blocks.length := by
  induction decomposition with
  | done =>
      rfl
  | step feature reduction tail ih =>
      cases feature <;>
        simp only [boundaryCount, crosscapCount, handleCount,
          blocks, ActionablePairReductionFeature.block,
          List.length_cons] at ih ⊢ <;>
        omega

/-- A decomposition of a nonempty word extracts at least one block. -/
theorem blocks_ne_nil_of_word_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word)
    (hne : word ≠ []) :
    decomposition.blocks ≠ [] := by
  cases decomposition with
  | done =>
      exact (hne rfl).elim
  | step =>
      simp [blocks]

/-- The normal form selected from a nonempty decomposition is Eval-admissible. -/
theorem normalForm_isEvalAdmissible_of_word_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word)
    (hne : word ≠ []) :
    decomposition.normalForm.IsEvalAdmissible := by
  have hblocks :
      0 < decomposition.blocks.length :=
    List.length_pos_iff_ne_nil.mpr
      (decomposition.blocks_ne_nil_of_word_ne_nil hne)
  have hsum := decomposition.count_sum_eq_blocks_length
  simp only [normalForm]
  split_ifs with hcrosscap
  · change 1 ≤ decomposition.handleCount ∨
      1 ≤ decomposition.boundaryCount
    rw [hcrosscap] at hsum
    omega
  · change
      1 ≤ decomposition.crosscapCount +
        2 * decomposition.handleCount
    omega

/-- Every edge recorded by a decomposition occurs in that decomposition's source word. -/
theorem mem_source_of_mem_extractedEdges {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word)
    (e : Fin n)
    (he : e ∈ decomposition.extractedEdges) :
    e ∈ word.map edgeOfDart := by
  induction decomposition with
  | done =>
      simp [extractedEdges] at he
  | step feature reduction tail ih =>
      simp only [extractedEdges, List.mem_append] at he
      rcases he with hfeature | htail
      · exact feature.extractedEdges_subset_source e hfeature
      · have hReduced :
            e ∈ reduction.reducedWord.map edgeOfDart :=
          ih htail
        have hResidual :=
          reduction.mem_source_of_mem e hReduced
        apply List.count_pos_iff.mp
        rw [feature.count_residualWord_of_mem e hResidual]
        exact List.count_pos_iff.mpr hResidual

/-- Distinct extraction steps consume disjoint edge names. -/
theorem extractedEdges_nodup {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word) :
    decomposition.extractedEdges.Nodup := by
  induction decomposition with
  | done =>
      simp [extractedEdges]
  | step feature reduction tail ih =>
      rw [extractedEdges, List.nodup_append]
      refine ⟨feature.extractedEdges_nodup, ih, ?_⟩
      intro e hfeature e' htail heq
      subst e'
      have hReduced :
          e ∈ reduction.reducedWord.map edgeOfDart :=
        tail.mem_source_of_mem_extractedEdges e htail
      have hResidual :=
        reduction.mem_source_of_mem e hReduced
      exact
        (List.disjoint_left.mp
          feature.extractedEdges_disjoint_residualWord)
          hfeature hResidual

end ResidualDecomposition

/-- One descent step from a directed opposite arc: either an immediately extractable feature,
or a strictly shorter opposite arc nested inside it. -/
inductive OppositeArcStep {n : ℕ}
    (word : List (SignedDart (Fin n))) {a : Fin n}
    (form : OppositeArcForm word a)
  | actionable (feature : ActionablePairReductionFeature word)
  | nested (b : Fin n) (inner : OppositeArcForm word b)
      (shorter : inner.between.length < form.between.length)

/-- Every once-used edge can be displayed at the cyclic head. -/
theorem exists_boundaryOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hcount : (word.map edgeOfDart).count a = 1) :
    Nonempty (BoundaryOccurrenceForm word a) := by
  rcases exists_decomposition_of_count_eq_one word a hcount with
    ⟨negative, left, right, hword, hleft, hright⟩
  let remainder := right ++ left
  have hrotation :
      word.IsRotated (dart a negative :: remainder) := by
    rw [hword]
    simpa only [remainder, List.cons_append,
      List.append_assoc] using
      (List.isRotated_append
        (l := left) (l' := dart a negative :: right))
  exact ⟨
    { negative := negative
      remainder := remainder
      rotated := hrotation
      edge_not_mem_remainder := by
        simp only [remainder, List.map_append,
          List.mem_append, not_or]
        exact ⟨hright, hleft⟩ }⟩

private theorem OppositeArcForm.exists_handleStep_of_second_in_remainder {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a) {d : SignedDart (Fin n)}
    {tail : List (SignedDart (Fin n))} (hbetween : form.between = d :: tail)
    (b : Fin n) (bNegative : Bool) (hd : d = dart b bNegative) (hba : b ≠ a)
    (hbTail : b ∉ tail.map edgeOfDart) (outsideNegative : Bool)
    (left right : List (SignedDart (Fin n)))
    (hremainder : form.remainder = left ++ dart b outsideNegative :: right)
    (hopposite : outsideNegative = !bNegative)
    (hbLeft : b ∉ left.map edgeOfDart) (hbRight : b ∉ right.map edgeOfDart) :
    Nonempty (OppositeArcStep word form) := by
  cases horientation : form.firstNegative
  · let handleForm : InterleavedOccurrenceForm word a b :=
      { bNegativeInside := bNegative
        beforeB := []
        beforeNegA := tail
        beforeOutsideB := left
        remainder := right
        rotated := by
          have hrotated := form.rotated
          rw [hbetween, hd, hremainder, hopposite, horientation] at hrotated
          simpa [dart, List.cons_append, List.append_assoc] using hrotated
        edge_ne := hba.symm
        a_not_mem_beforeB := by simp
        a_not_mem_beforeNegA := by
          intro haTail
          apply form.edge_not_mem_between
          rw [hbetween]
          simp [haTail]
        a_not_mem_beforeOutsideB := by
          intro haLeft
          apply form.edge_not_mem_remainder
          rw [hremainder]
          simp [haLeft]
        a_not_mem_remainder := by
          intro haRight
          apply form.edge_not_mem_remainder
          rw [hremainder]
          simp [haRight]
        b_not_mem_beforeB := by simp
        b_not_mem_beforeNegA := hbTail
        b_not_mem_beforeOutsideB := hbLeft
        b_not_mem_remainder := hbRight }
    exact ⟨.actionable (.handle a b handleForm)⟩
  · let handleForm : InterleavedOccurrenceForm word a b :=
      { bNegativeInside := outsideNegative
        beforeB := left
        beforeNegA := right
        beforeOutsideB := []
        remainder := tail
        rotated := by
          have hrotate :=
            List.isRotated_append
              (l := dart a form.firstNegative :: dart b bNegative :: tail)
              (l' := dart a (!form.firstNegative) :: left ++ dart b outsideNegative :: right)
          have hrotated := form.rotated
          rw [hbetween, hd, hremainder] at hrotated
          apply hrotated.trans
          simpa [dart, horientation, hopposite, List.cons_append, List.append_assoc] using hrotate
        edge_ne := hba.symm
        a_not_mem_beforeB := by
          intro haLeft
          apply form.edge_not_mem_remainder
          rw [hremainder]
          simp [haLeft]
        a_not_mem_beforeNegA := by
          intro haRight
          apply form.edge_not_mem_remainder
          rw [hremainder]
          simp [haRight]
        a_not_mem_beforeOutsideB := by simp
        a_not_mem_remainder := by
          intro haTail
          apply form.edge_not_mem_between
          rw [hbetween]
          simp [haTail]
        b_not_mem_beforeB := hbLeft
        b_not_mem_beforeNegA := hbRight
        b_not_mem_beforeOutsideB := by simp
        b_not_mem_remainder := hbTail }
    exact ⟨.actionable (.handle a b handleForm)⟩

/-- Inspect the first dart of a nonempty opposite arc.  A boundary or equal-orientation edge is
immediately actionable.  An opposite edge either crosses the selected pair, yielding a handle,
or closes inside it, yielding a strictly shorter directed arc. -/
theorem OppositeArcForm.exists_step_of_usedMultiplicities {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    Nonempty (OppositeArcStep word form) := by
  classical
  cases hbetween : form.between with
  | nil =>
      exact (form.between_ne_nil reduced hbetween).elim
  | cons d tail =>
      let b : Fin n := edgeOfDart d
      let bNegative : Bool := dartNegative d
      have hd : d = dart b bNegative := by
        exact (dart_edgeOfDart_dartNegative d).symm
      have hbmem : b ∈ form.between.map edgeOfDart := by
        rw [hbetween]
        simp [b]
      have hbword : b ∈ word.map edgeOfDart := by
        apply (form.rotated.map edgeOfDart).mem_iff.mpr
        simp [hbetween, b]
      have hba : b ≠ a := by
        intro h
        exact form.edge_not_mem_between (h ▸ hbmem)
      have hab : a ≠ b := hba.symm
      let pattern :=
        Classical.choice
          (exists_edgePattern_of_multiplicity
            word b (multiplicities b hbword))
      cases pattern with
      | boundary hcount =>
          let boundaryForm :=
            Classical.choice
              (exists_boundaryOccurrenceForm word b hcount)
          exact ⟨.actionable (.boundary b boundaryForm)⟩
      | positiveCrosscap hpositive hnegative =>
          let crosscapForm :=
            Classical.choice
              (exists_positiveCrosscapOccurrenceForm
                word b hpositive hnegative)
          exact ⟨.actionable (.crosscap b crosscapForm)⟩
      | negativeCrosscap hpositive hnegative =>
          let crosscapForm :=
            Classical.choice
              (exists_negativeCrosscapOccurrenceForm
                word b hpositive hnegative)
          exact ⟨.actionable (.crosscap b crosscapForm)⟩
      | opposite hpositive hnegative =>
          have htotal :
              (word.map edgeOfDart).count b = 2 := by
            rw [count_edgeOfDart_eq_pos_add_neg,
              hpositive, hnegative]
          have hrotatedCount :=
            (form.rotated.map edgeOfDart).perm.count_eq b
          have hsum :
              (tail.map edgeOfDart).count b +
                  (form.remainder.map edgeOfDart).count b = 1 := by
            rw [htotal] at hrotatedCount
            simp only [hbetween, List.map_cons, List.map_append,
              List.count_cons, List.count_append] at hrotatedCount
            rw [hd, edgeOfDart_dart, edgeOfDart_dart] at hrotatedCount
            simp [hab] at hrotatedCount
            omega
          by_cases hbTail : b ∈ tail.map edgeOfDart
          · have htailPositive :
                0 < (tail.map edgeOfDart).count b :=
              List.count_pos_iff.mpr hbTail
            have htailCount :
                (tail.map edgeOfDart).count b = 1 := by
              omega
            have hremainderCount :
                (form.remainder.map edgeOfDart).count b = 0 := by
              omega
            have hbRemainder :
                b ∉ form.remainder.map edgeOfDart :=
              List.count_eq_zero.mp hremainderCount
            rcases exists_decomposition_of_count_eq_one
                tail b htailCount with
              ⟨secondNegative, left, right, htail,
                hbLeft, hbRight⟩
            have hpositiveCount :=
              form.rotated.perm.count_eq (.pos b)
            have hnegativeCount :=
              form.rotated.perm.count_eq (.neg b)
            rw [hpositive] at hpositiveCount
            rw [hnegative] at hnegativeCount
            have hopposite :
                secondNegative = !bNegative := by
              cases hfirst : bNegative <;>
                cases hsecond : secondNegative
              · simp only [Bool.not_false]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, htail, dart, hfirst, hsecond,
                    haorientation, hab] at hpositiveCount
              · rfl
              · rfl
              · simp only [Bool.not_true]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, htail, dart, hfirst, hsecond,
                    haorientation, hab] at hnegativeCount
            let innerRemainder :=
              right ++
                dart a (!form.firstNegative) ::
                  form.remainder ++ [dart a form.firstNegative]
            have hrotateInner :
                word.IsRotated
                  (dart b bNegative :: left ++
                    dart b (!bNegative) :: innerRemainder) := by
              have hmoveA :=
                List.isRotated_append
                  (l := [dart a form.firstNegative])
                  (l' := dart b bNegative :: left ++
                    dart b (!bNegative) ::
                      (right ++
                        dart a (!form.firstNegative) ::
                          form.remainder))
              apply form.rotated.trans
              rw [hbetween, hd, htail, hopposite]
              simpa only [innerRemainder, List.nil_append,
                List.cons_append, List.append_assoc] using hmoveA
            let inner : OppositeArcForm word b :=
              { firstNegative := bNegative
                between := left
                remainder := innerRemainder
                rotated := hrotateInner
                edge_not_mem_between := hbLeft
                edge_not_mem_remainder := by
                  simp [innerRemainder, hba, hbRight, hbRemainder] }
            have hlength := congrArg List.length htail
            have hshorter :
                inner.between.length < form.between.length := by
              simp only [inner, hbetween, List.length_cons]
              simp only [List.length_append, List.length_cons] at hlength
              omega
            exact ⟨.nested b inner hshorter⟩
          · have htailCount :
                (tail.map edgeOfDart).count b = 0 :=
              List.count_eq_zero.mpr hbTail
            have hremainderCount :
                (form.remainder.map edgeOfDart).count b = 1 := by
              omega
            rcases exists_decomposition_of_count_eq_one
                form.remainder b hremainderCount with
              ⟨outsideNegative, left, right, hremainder,
                hbLeft, hbRight⟩
            have hpositiveCount :=
              form.rotated.perm.count_eq (.pos b)
            have hnegativeCount :=
              form.rotated.perm.count_eq (.neg b)
            rw [hpositive] at hpositiveCount
            rw [hnegative] at hnegativeCount
            have hopposite :
                outsideNegative = !bNegative := by
              cases hfirst : bNegative <;>
                cases hsecond : outsideNegative
              · simp only [Bool.not_false]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, hremainder, dart, hfirst, hsecond,
                    haorientation, hab] at hpositiveCount
              · rfl
              · rfl
              · simp only [Bool.not_true]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, hremainder, dart, hfirst, hsecond,
                    haorientation, hab] at hnegativeCount
            exact form.exists_handleStep_of_second_in_remainder hbetween b bNegative hd hba
              hbTail outsideNegative left right hremainder hopposite hbLeft hbRight

/-- Surface-valid words supply the residual multiplicity hypothesis required by one opposite-arc
descent step. -/
theorem OppositeArcForm.exists_step {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    Nonempty (OppositeArcStep word form) :=
  form.exists_step_of_usedMultiplicities
    (hasValidUsedMultiplicities_of_isSurfaceValid word valid) reduced

/-- Well-founded descent through nested opposite pairs terminates at a boundary, crosscap, or
interleaved handle feature. -/
noncomputable def OppositeArcForm.findActionableOfUsedMultiplicities {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    ActionablePairReductionFeature word := by
  let step :=
    Classical.choice
      (form.exists_step_of_usedMultiplicities
        multiplicities reduced)
  cases step with
  | actionable feature =>
      exact feature
  | nested b inner shorter =>
      exact inner.findActionableOfUsedMultiplicities
        multiplicities reduced
termination_by form.between.length
decreasing_by exact shorter

/-- Validity-specialized spelling of the residual opposite-arc descent. -/
noncomputable def OppositeArcForm.findActionable {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    ActionablePairReductionFeature word :=
  form.findActionableOfUsedMultiplicities
    (hasValidUsedMultiplicities_of_isSurfaceValid word valid) reduced

/-- In a pair-reduced word, the two darts of an opposite form have a nonempty intervening
word. -/
theorem OppositeOccurrenceForm.between_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeOccurrenceForm word a)
    (reduced : IsPairReduced word) :
    form.between ≠ [] := by
  intro hbetween
  rcases reduced with ⟨hreduced⟩
  exact hreduced
    { edge := a
      tail := form.remainder
      negativeFirst := false
      rotated := by
        simpa [inversePair, hbetween] using form.rotated }

/-! ### Proof-producing extraction of the easy pairing features -/

/-- The displayed cyclic word carried by an interleaved-pair certificate. -/
def InterleavedOccurrenceForm.displayedWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b) :
    List (SignedDart (Fin n)) :=
  .pos a :: form.beforeB ++
    dart b form.bNegativeInside :: form.beforeNegA ++
    .neg a :: form.beforeOutsideB ++
    dart b (!form.bNegativeInside) :: form.remainder

/-- The adjacent handle block produced by the three-Dyck extraction chain. -/
def InterleavedOccurrenceForm.groupedWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b) :
    List (SignedDart (Fin n)) :=
  [.pos a, .pos b, .neg a, .neg b] ++
    form.remainder ++ form.beforeOutsideB ++
    form.beforeNegA ++ form.beforeB

/-- When `b` is encountered negative inside the `a`-pair, reverse that edge to obtain the
positive-first source spelling required by handle extraction. -/
def InterleavedOccurrenceForm.negativeInsideSignedIso {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b)
    (hnegative : form.bNegativeInside = true) :
    SignedPresentationIso
      (Dyck.oneFace form.displayedWord)
      (Handle.source a b form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling b
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    have hposA :
        (Dyck.reverseEdgeRelabeling b).mapDart (.pos a) = .pos a :=
      Dyck.reverseEdgeRelabeling_of_ne b a form.edge_ne false
    have hnegA :
        (Dyck.reverseEdgeRelabeling b).mapDart (.neg a) = .neg a :=
      Dyck.reverseEdgeRelabeling_of_ne b a form.edge_ne true
    simp only [InterleavedOccurrenceForm.displayedWord,
      List.map_cons, List.map_append, hposA, hnegA,
      hnegative, Bool.not_true, dart,
      Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos]
    rw [Dyck.reverseEdgeRelabeling_word b form.beforeB
        form.b_not_mem_beforeB,
      Dyck.reverseEdgeRelabeling_word b form.beforeNegA
        form.b_not_mem_beforeNegA,
      Dyck.reverseEdgeRelabeling_word b form.beforeOutsideB
        form.b_not_mem_beforeOutsideB,
      Dyck.reverseEdgeRelabeling_word b form.remainder
        form.b_not_mem_remainder]
    convert List.IsRotated.refl _ using 1
    all_goals
      simp only [List.nil_append, List.cons_append, List.append_assoc]

/-- A certified interleaved pair produces an adjacent handle block through the existing
three-Dyck normalization chain.  If the inner occurrence of `b` is negative, the chain begins by
reversing the orientation assigned to `b`. -/
theorem InterleavedOccurrenceForm.exists_normalizationEquivalent_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ∃ validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.groupedWord, validGrouped⟩ := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated form.rotated
  let validDisplayed :
      (Dyck.oneFace form.displayedWord).IsSurfaceValid :=
    sourceRotation.isSurfaceValid valid
  have hToDisplayed :
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.displayedWord, validDisplayed⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  cases horientation : form.bNegativeInside
  · have hsource :
        Dyck.oneFace form.displayedWord =
          Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder := by
      simp [InterleavedOccurrenceForm.displayedWord,
        Handle.source, Dyck.source, dart, horientation,
        List.cons_append, List.append_assoc]
    let validSource :
        (Handle.source a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      hsource ▸ validDisplayed
    let validTarget :
        (Handle.target a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      Handle.target_isSurfaceValid a b form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder validSource
    have hHandle :
        NormalizationEquivalent
          ⟨Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validSource⟩
          ⟨Handle.target a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validTarget⟩ :=
      Handle.normalizationEquivalent a b
        form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder
        form.edge_ne
        form.a_not_mem_beforeB form.a_not_mem_beforeNegA
        form.a_not_mem_beforeOutsideB form.a_not_mem_remainder
        form.b_not_mem_beforeB form.b_not_mem_beforeNegA
        form.b_not_mem_beforeOutsideB form.b_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (Handle.target_boundary_isRotated_handle a b
          form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    have hDisplayed :
        (⟨Dyck.oneFace form.displayedWord, validDisplayed⟩ :
          ValidPresentation) =
          ⟨Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validSource⟩ :=
      ValidPresentation.ext hsource
    rw [hDisplayed] at hToDisplayed
    exact ⟨validGrouped,
      hToDisplayed.trans
        (hHandle.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩
  · let signIso := form.negativeInsideSignedIso horientation
    let validSource :
        (Handle.source a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      signIso.isSurfaceValid validDisplayed
    let validTarget :
        (Handle.target a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      Handle.target_isSurfaceValid a b form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder validSource
    have hHandle :
        NormalizationEquivalent
          ⟨Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validSource⟩
          ⟨Handle.target a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validTarget⟩ :=
      Handle.normalizationEquivalent a b
        form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder
        form.edge_ne
        form.a_not_mem_beforeB form.a_not_mem_beforeNegA
        form.a_not_mem_beforeOutsideB form.a_not_mem_remainder
        form.b_not_mem_beforeB form.b_not_mem_beforeNegA
        form.b_not_mem_beforeOutsideB form.b_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (Handle.target_boundary_isRotated_handle a b
          form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    exact ⟨validGrouped,
      hToDisplayed.trans
        ((NormalizationEquivalent.ofSignedIso signIso).trans
          (hHandle.trans
            (NormalizationEquivalent.ofSignedIso targetRotation)))⟩

/-- The cyclic spelling obtained by displaying a boundary edge at the head of its word. -/
def BoundaryOccurrenceForm.headWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : BoundaryOccurrenceForm word a) :
    List (SignedDart (Fin n)) :=
  dart a form.negative :: form.remainder

/-- Displaying a certified boundary occurrence at the head is already a normalization
equivalence: it is only a cyclic change of the distinguished face word. -/
theorem BoundaryOccurrenceForm.exists_normalizationEquivalent_head {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : BoundaryOccurrenceForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ∃ validHead : (Dyck.oneFace form.headWord).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.headWord, validHead⟩ := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated form.rotated
  let validHead :
      (Dyck.oneFace form.headWord).IsSurfaceValid :=
    rotation.isSurfaceValid valid
  exact ⟨validHead, NormalizationEquivalent.ofSignedIso rotation⟩

/-- The grouped spelling produced from a certified crosscap occurrence.  The segment after the
second occurrence is reversed, exactly as in the Gallier--Xu crosscap rewrite. -/
def CrosscapOccurrenceForm.groupedWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a) :
    List (SignedDart (Fin n)) :=
  [dart a form.negative, dart a form.negative] ++
    inverseWord form.remainder ++ form.between

/-- The positive crosscap target is cyclically the chosen grouped spelling. -/
theorem CrosscapOccurrenceForm.positiveTarget_isRotated_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a)
    (hpositive : form.negative = false) :
    (Crosscap.target a form.between form.remainder).boundary 0 |>.IsRotated
      form.groupedWord := by
  simp only [Crosscap.target, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := form.between)
      (l' := [SignedDart.pos a, SignedDart.pos a] ++
        inverseWord form.remainder)) using 1
  all_goals
    simp [CrosscapOccurrenceForm.groupedWord, dart, hpositive,
      List.cons_append, List.append_assoc]

/-- The negative crosscap target is cyclically the chosen grouped spelling. -/
theorem CrosscapOccurrenceForm.negativeTarget_isRotated_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a)
    (hnegative : form.negative = true) :
    (Crosscap.negativeTarget a form.between form.remainder).boundary 0 |>.IsRotated
      form.groupedWord := by
  simp only [Crosscap.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := form.between)
      (l' := [SignedDart.neg a, SignedDart.neg a] ++
        inverseWord form.remainder)) using 1
  all_goals
    simp [CrosscapOccurrenceForm.groupedWord, dart, hnegative,
      List.cons_append, List.append_assoc]

/-- A certified equally oriented pair can be moved to an adjacent crosscap block by an exact
normalization chain.  Both signs are supported; the grouped block retains the input sign. -/
theorem CrosscapOccurrenceForm.exists_normalizationEquivalent_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ∃ validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.groupedWord, validGrouped⟩ := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated form.rotated
  have hToDisplayed :
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace
            (dart a form.negative :: form.between ++
              dart a form.negative :: form.remainder),
          sourceRotation.isSurfaceValid valid⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  cases horientation : form.negative
  · have hsource :
        Dyck.oneFace
            (dart a form.negative :: form.between ++
              dart a form.negative :: form.remainder) =
          Crosscap.source a form.between form.remainder := by
      simp [Crosscap.source, dart, horientation,
        List.cons_append]
    let validSource :
        (Crosscap.source a form.between form.remainder).IsSurfaceValid :=
      hsource ▸ sourceRotation.isSurfaceValid valid
    let validTarget :
        (Crosscap.target a form.between form.remainder).IsSurfaceValid :=
      Crosscap.target_isSurfaceValid a form.between form.remainder validSource
    have hCrosscap :
        NormalizationEquivalent
          ⟨Crosscap.source a form.between form.remainder, validSource⟩
          ⟨Crosscap.target a form.between form.remainder, validTarget⟩ :=
      Crosscap.normalizationEquivalent a form.between form.remainder
        form.edge_not_mem_between form.edge_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (form.positiveTarget_isRotated_grouped horientation)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    have hDisplayed :
        (⟨Dyck.oneFace
              (dart a form.negative :: form.between ++
                dart a form.negative :: form.remainder),
            sourceRotation.isSurfaceValid valid⟩ :
          ValidPresentation) =
          ⟨Crosscap.source a form.between form.remainder, validSource⟩ :=
      ValidPresentation.ext hsource
    rw [hDisplayed] at hToDisplayed
    exact ⟨validGrouped,
      hToDisplayed.trans
        (hCrosscap.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩
  · have hsource :
        Dyck.oneFace
            (dart a form.negative :: form.between ++
              dart a form.negative :: form.remainder) =
          Crosscap.negativeSource a form.between form.remainder := by
      simp [Crosscap.negativeSource, dart, horientation,
        List.cons_append]
    let validSource :
        (Crosscap.negativeSource a form.between form.remainder).IsSurfaceValid :=
      hsource ▸ sourceRotation.isSurfaceValid valid
    let validTarget :
        (Crosscap.negativeTarget a form.between form.remainder).IsSurfaceValid :=
      Crosscap.negativeTarget_isSurfaceValid
        a form.between form.remainder validSource
    have hCrosscap :
        NormalizationEquivalent
          ⟨Crosscap.negativeSource a form.between form.remainder, validSource⟩
          ⟨Crosscap.negativeTarget a form.between form.remainder, validTarget⟩ :=
      Crosscap.negativeNormalizationEquivalent
        a form.between form.remainder
        form.edge_not_mem_between form.edge_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (form.negativeTarget_isRotated_grouped horientation)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    have hDisplayed :
        (⟨Dyck.oneFace
              (dart a form.negative :: form.between ++
                dart a form.negative :: form.remainder),
            sourceRotation.isSurfaceValid valid⟩ :
          ValidPresentation) =
          ⟨Crosscap.negativeSource a form.between form.remainder,
            validSource⟩ :=
      ValidPresentation.ext hsource
    rw [hDisplayed] at hToDisplayed
    exact ⟨validGrouped,
      hToDisplayed.trans
        (hCrosscap.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩

/-- Each local extraction target is definitionally its extracted block followed by the residual
word used by the global recursion. -/
theorem ActionablePairReductionFeature.block_word_append_residualWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.block.word ++ feature.residualWord =
      match feature with
      | .boundary _ form => form.headWord
      | .crosscap _ form => form.groupedWord
      | .handle _ _ form => form.groupedWord := by
  cases feature <;>
    simp [ActionablePairReductionFeature.block,
      ExtractedBlock.word,
      ActionablePairReductionFeature.residualWord,
      BoundaryOccurrenceForm.headWord,
      CrosscapOccurrenceForm.groupedWord,
      InterleavedOccurrenceForm.groupedWord,
      List.append_assoc]

/-- A proof-producing result of acting on one certified pairing feature.  The constructor records
the exact extracted spelling, its transported validity, and the normalization chain from the
original word. -/
inductive ActionablePairReductionResult {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
  | boundary (a : Fin n) (form : BoundaryOccurrenceForm word a)
      (validHead : (Dyck.oneFace form.headWord).IsSurfaceValid)
      (equivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace word, valid⟩
          ⟨Dyck.oneFace form.headWord, validHead⟩)
  | crosscap (a : Fin n) (form : CrosscapOccurrenceForm word a)
      (validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid)
      (equivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace word, valid⟩
          ⟨Dyck.oneFace form.groupedWord, validGrouped⟩)
  | handle (a b : Fin n) (form : InterleavedOccurrenceForm word a b)
      (validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid)
      (equivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace word, valid⟩
          ⟨Dyck.oneFace form.groupedWord, validGrouped⟩)

namespace ActionablePairReductionResult

/-- Feature whose local normalization chain was executed. -/
def feature {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid} :
    ActionablePairReductionResult word valid →
      ActionablePairReductionFeature word
  | .boundary a form _ _ => .boundary a form
  | .crosscap a form _ _ => .crosscap a form
  | .handle a b form _ _ => .handle a b form

/-- Exact block-plus-residual word reached by an executed extraction. -/
def targetWord {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    List (SignedDart (Fin n)) :=
  result.feature.block.word ++ result.feature.residualWord

/-- Valid presentation reached by one actionable extraction. -/
def target {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid} :
    ActionablePairReductionResult word valid → ValidPresentation
  | .boundary _ form validHead _ =>
      ⟨Dyck.oneFace form.headWord, validHead⟩
  | .crosscap _ form validGrouped _ =>
      ⟨Dyck.oneFace form.groupedWord, validGrouped⟩
  | .handle _ _ form validGrouped _ =>
      ⟨Dyck.oneFace form.groupedWord, validGrouped⟩

/-- The stored target presentation is the one-face presentation on `targetWord`. -/
theorem target_presentation_eq_oneFace_targetWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    result.target.presentation = Dyck.oneFace result.targetWord := by
  cases result <;>
    simp [target, targetWord, feature,
      ActionablePairReductionFeature.block_word_append_residualWord]

/-- Validity witness for the exact block-plus-residual target word. -/
theorem targetWordValid {n : ℕ}
    {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    (Dyck.oneFace result.targetWord).IsSurfaceValid :=
  result.target_presentation_eq_oneFace_targetWord ▸ result.target.valid

/-- Normalization equivalence certified by one actionable extraction. -/
theorem equivalent {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, valid⟩ result.target := by
  cases result with
  | boundary _ _ _ equivalent => exact equivalent
  | crosscap _ _ _ equivalent => exact equivalent
  | handle _ _ _ _ equivalent => exact equivalent

/-- Normalization equivalence to the stable exact block-plus-residual spelling. -/
theorem equivalent_to_targetWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, valid⟩
      ⟨Dyck.oneFace result.targetWord, result.targetWordValid⟩ := by
  have hnode :
      result.target =
        ⟨Dyck.oneFace result.targetWord,
          result.targetWordValid⟩ := by
    apply ValidPresentation.ext
    exact result.target_presentation_eq_oneFace_targetWord
  rw [← hnode]
  exact result.equivalent

end ActionablePairReductionResult

/-- Execute an actionable pairing feature using the corresponding proof-producing rewrite
endpoint. -/
noncomputable def ActionablePairReductionFeature.extract {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ActionablePairReductionResult word valid := by
  cases feature with
  | boundary a form =>
      let witness :=
        form.exists_normalizationEquivalent_head valid
      let validHead := Classical.choose witness
      let equivalent := Classical.choose_spec witness
      exact .boundary a form validHead equivalent
  | crosscap a form =>
      let witness :=
        form.exists_normalizationEquivalent_grouped valid
      let validGrouped := Classical.choose witness
      let equivalent := Classical.choose_spec witness
      exact .crosscap a form validGrouped equivalent
  | handle a b form =>
      let witness :=
        form.exists_normalizationEquivalent_grouped valid
      let validGrouped := Classical.choose witness
      let equivalent := Classical.choose_spec witness
      exact .handle a b form validGrouped equivalent

@[simp]
theorem ActionablePairReductionFeature.feature_extract {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    (feature.extract valid).feature = feature := by
  cases feature <;>
    simp [ActionablePairReductionFeature.extract,
      ActionablePairReductionResult.feature]

@[simp]
theorem ActionablePairReductionFeature.targetWord_extract {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    (feature.extract valid).targetWord =
      feature.block.word ++ feature.residualWord := by
  simp [ActionablePairReductionResult.targetWord]

/-- Proof-producing execution of an extraction on a marked word, with the exact marked target
retained as its public endpoint. -/
structure MarkedActionablePairReductionResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (valid :
      (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand marked.targetTokens)).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated marked.targetTokens
  targetClassified :
    ReductionToken.AllClassified marked.targetTokens
  targetProtectedNodup :
    (ReductionToken.protectedNames
      marked.targetTokens).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand marked.targetTokens),
        targetValid⟩

namespace MarkedActionablePairReductionFeature

/-- Execute a marked feature by expanding it, applying the corresponding Gallier--Xu move, and
transporting the result back to the exact marked target spelling. -/
theorem extract {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup)
    (valid :
      (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedActionablePairReductionResult marked valid := by
  let result :=
    (marked.expandedFeature separated).extract valid
  have htarget :
      result.targetWord =
        ReductionToken.expand marked.targetTokens := by
    rw [ActionablePairReductionFeature.targetWord_extract]
    exact
      marked.expandedFeature_block_word_append_residualWord
        separated
  have targetValid :
      (Dyck.oneFace
        (ReductionToken.expand marked.targetTokens)).IsSurfaceValid := by
    rw [← htarget]
    exact result.targetWordValid
  refine
    { targetValid := targetValid
      targetSeparated :=
        marked.targetTokens_isSeparated separated
      targetClassified :=
        marked.targetTokens_allClassified classified
      targetProtectedNodup :=
        marked.targetTokens_protectedNames_nodup
          separated protectedNodup
      equivalent := ?_ }
  have hequivalent := result.equivalent_to_targetWord
  simpa only [htarget] using hequivalent

end MarkedActionablePairReductionFeature

namespace MarkedCancellablePair

/-- Exact lowered marked endpoint of an adjacent inverse-pair cancellation. -/
noncomputable def cancellationTargetTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedCancellablePair tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    List (ReductionToken n) :=
  ReductionToken.lowerTokensAvoiding pair.edge
    pair.tailTokens (pair.edge_not_mem_tailTokens valid)

end MarkedCancellablePair

/-- Proof-producing cancellation of a token-adjacent inverse pair, retaining the lowered marked
target rather than flattening previously extracted blocks. -/
structure MarkedCancellationResult {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedCancellablePair tokens)
    (valid :
      (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand
        (pair.cancellationTargetTokens valid))).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated
      (pair.cancellationTargetTokens valid)
  targetClassified :
    ReductionToken.AllClassified
      (pair.cancellationTargetTokens valid)
  targetProtectedNodup :
    (ReductionToken.protectedNames
      (pair.cancellationTargetTokens valid)).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand
          (pair.cancellationTargetTokens valid)),
        targetValid⟩

namespace MarkedCancellablePair

/-- Execute an inverse pair which is genuinely adjacent in the marked word.  The nonempty-tail
hypothesis selects the ordinary cancellation endpoint; the empty-tail sphere endpoint remains
handled by the outer cancellation recursion. -/
theorem cancel {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedCancellablePair tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup)
    (valid :
      (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid)
    (tail_nonempty :
      ReductionToken.expand pair.tailTokens ≠ []) :
    MarkedCancellationResult pair valid := by
  let ha := pair.edge_not_mem_tailTokens valid
  let targetTokens := pair.cancellationTargetTokens valid
  have tailClassified :
      ReductionToken.AllClassified pair.tailTokens := by
    have displayed :=
      classified.of_isRotated pair.rotated
    intro token htoken
    exact displayed token (by simp [htoken])
  have targetClassified :
      ReductionToken.AllClassified targetTokens :=
    by
      dsimp [targetTokens,
        MarkedCancellablePair.cancellationTargetTokens]
      exact
        tailClassified.lowerTokensAvoiding
          pair.edge pair.tailTokens ha
  have targetSeparated :
      ReductionToken.IsSeparated targetTokens :=
    by
      dsimp [targetTokens,
        MarkedCancellablePair.cancellationTargetTokens]
      exact
        (pair.tailTokens_isSeparated separated).lowerTokensAvoiding
          pair.edge pair.tailTokens ha
  have targetProtectedNodup :
      (ReductionToken.protectedNames targetTokens).Nodup :=
    by
      dsimp [targetTokens,
        MarkedCancellablePair.cancellationTargetTokens]
      exact
        ReductionToken.protectedNames_nodup_lowerTokensAvoiding
          pair.edge pair.tailTokens ha
          (pair.tailTokens_protectedNames_nodup protectedNodup)
  have htarget :
      ReductionToken.expand targetTokens =
        Cancellation.lowerTail pair.edge
          (ReductionToken.expand pair.tailTokens) := by
    exact ReductionToken.expand_lowerTokensAvoiding
      pair.edge pair.tailTokens ha
  have hlower :
      Cancellation.lowerTail pair.edge
          (ReductionToken.expand pair.tailTokens) ≠ [] :=
    Cancellation.lowerTail_ne_nil_of_ne_nil
      pair.edge (ReductionToken.expand pair.tailTokens)
      ha tail_nonempty
  cases hnegative : pair.negativeFirst
  · have hrotated :
        (ReductionToken.expand tokens).IsRotated
          ([.pos pair.edge, .neg pair.edge] ++
            ReductionToken.expand pair.tailTokens) := by
      have hexpanded :=
        ReductionToken.expand_isRotated pair.rotated
      simpa [dart, hnegative] using hexpanded
    let validTarget :
        (Cancellation.target
          (Cancellation.lowerTail pair.edge
            (ReductionToken.expand
              pair.tailTokens))).IsSurfaceValid :=
      Cancellation.target_isSurfaceValid
        (Cancellation.lowerTail pair.edge
          (ReductionToken.expand pair.tailTokens))
        hlower
        ((Cancellation.namedSourceSignedIso pair.edge
          (ReductionToken.expand pair.tailTokens) ha).isSurfaceValid
          ((Dyck.oneFaceSignedIsoOfIsRotated
            hrotated).isSurfaceValid valid))
    have targetValid :
        (Dyck.oneFace
          (ReductionToken.expand targetTokens)).IsSurfaceValid := by
      rw [htarget]
      exact validTarget
    refine
      { targetValid := by
          simpa [targetTokens] using targetValid
        targetSeparated := targetSeparated
        targetClassified := targetClassified
        targetProtectedNodup := targetProtectedNodup
        equivalent := ?_ }
    have hequivalent :=
      Cancellation.normalizationEquivalentOfIsRotated
        (ReductionToken.expand tokens) pair.edge
        (ReductionToken.expand pair.tailTokens)
        hrotated ha hlower valid
    have htargetTokens :
        pair.cancellationTargetTokens valid =
          targetTokens := rfl
    simpa only [htargetTokens, htarget] using hequivalent
  · have hrotated :
        (ReductionToken.expand tokens).IsRotated
          ([.neg pair.edge, .pos pair.edge] ++
            ReductionToken.expand pair.tailTokens) := by
      have hexpanded :=
        ReductionToken.expand_isRotated pair.rotated
      simpa [dart, hnegative] using hexpanded
    let validTarget :
        (Cancellation.target
          (Cancellation.lowerTail pair.edge
            (ReductionToken.expand
              pair.tailTokens))).IsSurfaceValid :=
      Cancellation.target_isSurfaceValid
        (Cancellation.lowerTail pair.edge
          (ReductionToken.expand pair.tailTokens))
        hlower
        ((Cancellation.namedSourceSignedIso pair.edge
          (ReductionToken.expand pair.tailTokens) ha).isSurfaceValid
          ((Cancellation.negativeNamedSourceSignedIso
            pair.edge
            (ReductionToken.expand pair.tailTokens) ha).isSurfaceValid
            ((Dyck.oneFaceSignedIsoOfIsRotated
              hrotated).isSurfaceValid valid)))
    have targetValid :
        (Dyck.oneFace
          (ReductionToken.expand targetTokens)).IsSurfaceValid := by
      rw [htarget]
      exact validTarget
    refine
      { targetValid := by
          simpa [targetTokens] using targetValid
        targetSeparated := targetSeparated
        targetClassified := targetClassified
        targetProtectedNodup := targetProtectedNodup
        equivalent := ?_ }
    have hequivalent :=
      Cancellation.negativeNormalizationEquivalentOfIsRotated
        (ReductionToken.expand tokens) pair.edge
        (ReductionToken.expand pair.tailTokens)
        hrotated ha hlower valid
    have htargetTokens :
        pair.cancellationTargetTokens valid =
          targetTokens := rfl
    simpa only [htargetTokens, htarget] using hequivalent

end MarkedCancellablePair

/-- Proof-producing reclassification of a residual inverse pair and boundary singleton as one
atomic protected loop. -/
structure MarkedBoundaryClosureResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens)
    (valid :
      (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand closure.targetTokens)).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated closure.targetTokens
  targetClassified :
    ReductionToken.AllClassified closure.targetTokens
  targetProtectedNodup :
    (ReductionToken.protectedNames
      closure.targetTokens).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand closure.targetTokens),
        targetValid⟩

namespace MarkedBoundaryClosure

/-- Close an extracted boundary singleton into an atomic loop.  The underlying signed word changes
only by cyclic rotation, while the residual measure drops by the two carrier darts. -/
theorem close {n : ℕ}
    {tokens : List (ReductionToken n)}
    (closure : MarkedBoundaryClosure tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup)
    (valid :
      (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedBoundaryClosureResult closure valid := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      closure.expand_isRotated_target
  let targetValid :
      (Dyck.oneFace
        (ReductionToken.expand
          closure.targetTokens)).IsSurfaceValid :=
    rotation.isSurfaceValid valid
  exact
    { targetValid := targetValid
      targetSeparated :=
        closure.targetTokens_isSeparated separated valid
      targetClassified :=
        closure.targetTokens_allClassified classified
      targetProtectedNodup :=
        closure.targetTokens_protectedNames_nodup
          separated valid protectedNodup
      equivalent :=
        NormalizationEquivalent.ofSignedIso rotation }

end MarkedBoundaryClosure

/-- Proof-producing Dyck rotation of a raw boundary atom behind a protected interval. -/
structure MarkedBoundaryAtomRotateResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand step.targetTokens)).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated step.targetTokens
  targetClassified :
    ReductionToken.AllClassified step.targetTokens
  targetProtectedNodup :
    (ReductionToken.protectedNames
      step.targetTokens).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand step.targetTokens),
        targetValid⟩

namespace MarkedBoundaryAtomRotate

/-- Execute the raw-boundary rotation through the exact signed Dyck chain. -/
theorem rotate {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryAtomRotate tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedBoundaryAtomRotateResult step valid := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      step.expand_isRotated_sourceWord
  let validSourceWord :
      (Dyck.oneFace
        (BoundaryAtomRotate.sourceWord
          step.carrier step.hole step.carrierNegative
          step.holeNegative
          (ReductionToken.expand step.insideTokens)
          (ReductionToken.expand
            step.outsideTokens))).IsSurfaceValid :=
    sourceRotation.isSurfaceValid valid
  let witness :=
    BoundaryAtomRotate.exists_normalizationEquivalent
      step.carrier step.hole step.carrierNegative
      step.holeNegative
      (ReductionToken.expand step.insideTokens)
      (ReductionToken.expand step.outsideTokens)
      step.carrier_ne_hole
      step.carrier_not_mem_inside
      step.carrier_not_mem_outside
      validSourceWord
  let validTargetWord := Classical.choose witness
  have hequivalentWord := Classical.choose_spec witness
  have htarget :
      ReductionToken.expand step.targetTokens =
        BoundaryAtomRotate.targetWord
          step.carrier step.hole step.carrierNegative
          step.holeNegative
          (ReductionToken.expand step.insideTokens)
          (ReductionToken.expand step.outsideTokens) :=
    step.expand_targetTokens
  have targetValid :
      (Dyck.oneFace
        (ReductionToken.expand
          step.targetTokens)).IsSurfaceValid := by
    rw [htarget]
    exact validTargetWord
  refine
    { targetValid := targetValid
      targetSeparated :=
        step.targetTokens_isSeparated separated
      targetClassified :=
        step.targetTokens_allClassified classified
      targetProtectedNodup :=
        step.targetTokens_protectedNames_nodup
          protectedNodup
      equivalent := ?_ }
  have hrotation :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (ReductionToken.expand tokens), valid⟩
        ⟨Dyck.oneFace
          (BoundaryAtomRotate.sourceWord
            step.carrier step.hole step.carrierNegative
            step.holeNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand step.outsideTokens)),
          validSourceWord⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  have hchain := hrotation.trans hequivalentWord
  simpa only [htarget] using hchain

end MarkedBoundaryAtomRotate

/-- Proof-producing commute of one completed boundary loop out of a contextual residual pair. -/
structure MarkedBoundaryBlockCommuteResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedBoundaryBlockCommute tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand commute.targetTokens)).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated commute.targetTokens
  targetClassified :
    ReductionToken.AllClassified commute.targetTokens
  targetProtectedNodup :
    (ReductionToken.protectedNames
      commute.targetTokens).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand commute.targetTokens),
        targetValid⟩

namespace MarkedBoundaryBlockCommute

/-- Execute the contextual boundary-loop commute through the exact word-level `LoopGrouping`
chain, supporting either orientation of the loop carrier. -/
theorem commute {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedBoundaryBlockCommute tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedBoundaryBlockCommuteResult step valid := by
  cases hnegative : step.carrierNegative
  · have hsource :
        (ReductionToken.expand tokens).IsRotated
          (BoundaryBlockCommute.sourceWord
            step.outer step.carrier step.hole
            step.outerNegative step.holeNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand step.outsideTokens)) := by
      simpa [hnegative] using step.expand_isRotated_sourceWord
    let sourceRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated hsource
    let validSourceWord :
        (Dyck.oneFace
          (BoundaryBlockCommute.sourceWord
            step.outer step.carrier step.hole
            step.outerNegative step.holeNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand
              step.outsideTokens))).IsSurfaceValid :=
      sourceRotation.isSurfaceValid valid
    let witness :=
      BoundaryBlockCommute.exists_positiveNormalizationEquivalent
        step.outer step.carrier step.hole
        step.outerNegative step.holeNegative
        (ReductionToken.expand step.insideTokens)
        (ReductionToken.expand step.outsideTokens)
        step.carrier_ne_hole step.carrier_ne_outer
        step.carrier_not_mem_inside
        step.carrier_not_mem_outside validSourceWord
    let validTargetWord := Classical.choose witness
    have hequivalentWord := Classical.choose_spec witness
    have htarget :
        ReductionToken.expand step.targetTokens =
          BoundaryBlockCommute.targetWord
            step.outer step.carrier step.hole
            step.outerNegative step.holeNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand step.outsideTokens) := by
      simpa [hnegative] using step.expand_targetTokens
    have targetValid :
        (Dyck.oneFace
          (ReductionToken.expand
            step.targetTokens)).IsSurfaceValid := by
      rw [htarget]
      exact validTargetWord
    refine
      { targetValid := targetValid
        targetSeparated :=
          step.targetTokens_isSeparated separated
        targetClassified :=
          step.targetTokens_allClassified classified
        targetProtectedNodup :=
          step.targetTokens_protectedNames_nodup
            protectedNodup
        equivalent := ?_ }
    have hrotation :
        NormalizationEquivalent
          ⟨Dyck.oneFace
            (ReductionToken.expand tokens), valid⟩
          ⟨Dyck.oneFace
            (BoundaryBlockCommute.sourceWord
              step.outer step.carrier step.hole
              step.outerNegative step.holeNegative
              (ReductionToken.expand step.insideTokens)
              (ReductionToken.expand step.outsideTokens)),
            validSourceWord⟩ :=
      NormalizationEquivalent.ofSignedIso sourceRotation
    have hchain := hrotation.trans hequivalentWord
    simpa only [htarget] using hchain
  · have hsource :
        (ReductionToken.expand tokens).IsRotated
          (BoundaryBlockCommute.negativeSourceWord
            step.outer step.carrier step.hole
            step.outerNegative step.holeNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand step.outsideTokens)) := by
      simpa [hnegative] using step.expand_isRotated_sourceWord
    let sourceRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated hsource
    let validSourceWord :
        (Dyck.oneFace
          (BoundaryBlockCommute.negativeSourceWord
            step.outer step.carrier step.hole
            step.outerNegative step.holeNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand
              step.outsideTokens))).IsSurfaceValid :=
      sourceRotation.isSurfaceValid valid
    let witness :=
      BoundaryBlockCommute.exists_negativeNormalizationEquivalent
        step.outer step.carrier step.hole
        step.outerNegative step.holeNegative
        (ReductionToken.expand step.insideTokens)
        (ReductionToken.expand step.outsideTokens)
        step.carrier_ne_hole step.carrier_ne_outer
        step.carrier_not_mem_inside
        step.carrier_not_mem_outside validSourceWord
    let validTargetWord := Classical.choose witness
    have hequivalentWord := Classical.choose_spec witness
    have htarget :
        ReductionToken.expand step.targetTokens =
          BoundaryBlockCommute.negativeTargetWord
            step.outer step.carrier step.hole
            step.outerNegative step.holeNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand step.outsideTokens) := by
      simpa [hnegative] using step.expand_targetTokens
    have targetValid :
        (Dyck.oneFace
          (ReductionToken.expand
            step.targetTokens)).IsSurfaceValid := by
      rw [htarget]
      exact validTargetWord
    refine
      { targetValid := targetValid
        targetSeparated :=
          step.targetTokens_isSeparated separated
        targetClassified :=
          step.targetTokens_allClassified classified
        targetProtectedNodup :=
          step.targetTokens_protectedNames_nodup
            protectedNodup
        equivalent := ?_ }
    have hrotation :
        NormalizationEquivalent
          ⟨Dyck.oneFace
            (ReductionToken.expand tokens), valid⟩
          ⟨Dyck.oneFace
            (BoundaryBlockCommute.negativeSourceWord
              step.outer step.carrier step.hole
              step.outerNegative step.holeNegative
              (ReductionToken.expand step.insideTokens)
              (ReductionToken.expand step.outsideTokens)),
            validSourceWord⟩ :=
      NormalizationEquivalent.ofSignedIso sourceRotation
    have hchain := hrotation.trans hequivalentWord
    simpa only [htarget] using hchain

end MarkedBoundaryBlockCommute

/-- Proof-producing commute of one completed crosscap through a contextual residual pair. -/
structure MarkedCrosscapBlockCommuteResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedCrosscapBlockCommute tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand commute.targetTokens)).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated commute.targetTokens
  targetClassified :
    ReductionToken.AllClassified commute.targetTokens
  targetProtectedNodup :
    (ReductionToken.protectedNames
      commute.targetTokens).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand commute.targetTokens),
        targetValid⟩

namespace MarkedCrosscapBlockCommute

/-- Execute contextual crosscap commuting through the exact two-crosscap word chain. -/
theorem commute {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedCrosscapBlockCommute tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedCrosscapBlockCommuteResult step valid := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      step.expand_isRotated_sourceWord
  let validSourceWord :
      (Dyck.oneFace
        (CrosscapBlockCommute.sourceWord
          step.outer step.carrier
          step.outerNegative step.carrierNegative
          (ReductionToken.expand step.insideTokens)
          (ReductionToken.expand
            step.outsideTokens))).IsSurfaceValid :=
    sourceRotation.isSurfaceValid valid
  let witness :=
    CrosscapBlockCommute.exists_normalizationEquivalent
      step.outer step.carrier
      step.outerNegative step.carrierNegative
      (ReductionToken.expand step.insideTokens)
      (ReductionToken.expand step.outsideTokens)
      step.carrier_ne_outer
      step.carrier_not_mem_inside
      step.carrier_not_mem_outside
      step.outer_not_mem_inside
      step.outer_not_mem_outside
      validSourceWord
  let validTargetWord := Classical.choose witness
  have hequivalentWord :=
    Classical.choose_spec witness
  have htarget :
      ReductionToken.expand step.targetTokens =
        CrosscapBlockCommute.targetWord
          step.outer step.carrier
          step.outerNegative step.carrierNegative
          (ReductionToken.expand step.insideTokens)
          (ReductionToken.expand
            step.outsideTokens) :=
    step.expand_targetTokens
  have targetValid :
      (Dyck.oneFace
        (ReductionToken.expand
          step.targetTokens)).IsSurfaceValid := by
    rw [htarget]
    exact validTargetWord
  refine
    { targetValid := targetValid
      targetSeparated :=
        step.targetTokens_isSeparated separated
      targetClassified :=
        step.targetTokens_allClassified classified
      targetProtectedNodup :=
        step.targetTokens_protectedNames_nodup
          protectedNodup
      equivalent := ?_ }
  have hrotation :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (ReductionToken.expand tokens), valid⟩
        ⟨Dyck.oneFace
          (CrosscapBlockCommute.sourceWord
            step.outer step.carrier
            step.outerNegative step.carrierNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand
              step.outsideTokens)),
          validSourceWord⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  have hchain := hrotation.trans hequivalentWord
  simpa only [htarget] using hchain

end MarkedCrosscapBlockCommute

/-- Proof-producing commute of one completed handle through a contextual residual pair. -/
structure MarkedHandleBlockCommuteResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (commute : MarkedHandleBlockCommute tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand commute.targetTokens)).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated commute.targetTokens
  targetClassified :
    ReductionToken.AllClassified commute.targetTokens
  targetProtectedNodup :
    (ReductionToken.protectedNames
      commute.targetTokens).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand commute.targetTokens),
        targetValid⟩

namespace MarkedHandleBlockCommute

/-- Execute contextual handle commuting through the exact four-Dyck word chain. -/
theorem commute {n : ℕ}
    {tokens : List (ReductionToken n)}
    (step : MarkedHandleBlockCommute tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup :
      (ReductionToken.protectedNames tokens).Nodup)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedHandleBlockCommuteResult step valid := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      step.expand_isRotated_sourceWord
  let validSourceWord :
      (Dyck.oneFace
        (HandleBlockCommute.sourceWord
          step.outer step.first step.second
          step.outerNegative
          (ReductionToken.expand step.insideTokens)
          (ReductionToken.expand
            step.outsideTokens))).IsSurfaceValid :=
    sourceRotation.isSurfaceValid valid
  let witness :=
    HandleBlockCommute.exists_normalizationEquivalent
      step.outer step.first step.second
      step.outerNegative
      (ReductionToken.expand step.insideTokens)
      (ReductionToken.expand step.outsideTokens)
      step.first_ne_second
      step.first_ne_outer step.second_ne_outer
      step.first_not_mem_inside
      step.first_not_mem_outside
      step.second_not_mem_inside
      step.second_not_mem_outside
      step.outer_not_mem_inside
      step.outer_not_mem_outside
      validSourceWord
  let validTargetWord := Classical.choose witness
  have hequivalentWord :=
    Classical.choose_spec witness
  have htarget :
      ReductionToken.expand step.targetTokens =
        HandleBlockCommute.targetWord
          step.outer step.first step.second
          step.outerNegative
          (ReductionToken.expand step.insideTokens)
          (ReductionToken.expand
            step.outsideTokens) :=
    step.expand_targetTokens
  have targetValid :
      (Dyck.oneFace
        (ReductionToken.expand
          step.targetTokens)).IsSurfaceValid := by
    rw [htarget]
    exact validTargetWord
  refine
    { targetValid := targetValid
      targetSeparated :=
        step.targetTokens_isSeparated separated
      targetClassified :=
        step.targetTokens_allClassified classified
      targetProtectedNodup :=
        step.targetTokens_protectedNames_nodup
          protectedNodup
      equivalent := ?_ }
  have hrotation :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (ReductionToken.expand tokens), valid⟩
        ⟨Dyck.oneFace
          (HandleBlockCommute.sourceWord
            step.outer step.first step.second
            step.outerNegative
            (ReductionToken.expand step.insideTokens)
            (ReductionToken.expand
              step.outsideTokens)),
          validSourceWord⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  have hchain := hrotation.trans hequivalentWord
  simpa only [htarget] using hchain

end MarkedHandleBlockCommute

/-- Proof-producing contraction of two adjacent extracted boundary subdivisions. -/
structure MarkedBoundaryPairContractionResult {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (contraction : MarkedBoundaryPairContraction tokens)
    (valid :
      (Dyck.oneFace
        (ReductionToken.expand tokens)).IsSurfaceValid) :
    Prop where
  targetValid :
    (Dyck.oneFace
      (ReductionToken.expand
        contraction.targetTokens)).IsSurfaceValid
  targetSeparated :
    ReductionToken.IsSeparated contraction.targetTokens
  targetClassified :
    ReductionToken.AllClassified contraction.targetTokens
  targetProtectedNodup :
    (ReductionToken.protectedNames
      contraction.targetTokens).Nodup
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens), valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand contraction.targetTokens),
        targetValid⟩

namespace MarkedBoundaryPairContraction

/-- Execute one adjacent-boundary P1 contraction, lowering the ambient edge type by one. -/
theorem contract {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (step : MarkedBoundaryPairContraction tokens)
    (separated : ReductionToken.IsSeparated tokens)
    (classified : ReductionToken.AllClassified tokens)
    (protectedNodup : (ReductionToken.protectedNames tokens).Nodup)
    (valid : (Dyck.oneFace (ReductionToken.expand tokens)).IsSurfaceValid) :
    MarkedBoundaryPairContractionResult step valid := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated step.expand_isRotated_sourceWord
  let validSourceWord :
      (Dyck.oneFace
        (BoundaryPairContraction.sourceWord
          step.first step.second
          step.firstNegative step.secondNegative
          (ReductionToken.expand step.tailTokens))).IsSurfaceValid :=
    sourceRotation.isSurfaceValid valid
  let witness :=
    BoundaryPairContraction.exists_normalizationEquivalent
      step.first step.second step.firstNegative step.secondNegative
      (ReductionToken.expand step.tailTokens)
      step.first_ne_second step.first_not_mem_tail step.second_not_mem_tail validSourceWord
  let validTargetWord := Classical.choose witness
  have hequivalentWord :=
    Classical.choose_spec witness
  have htarget :
      ReductionToken.expand step.targetTokens =
        BoundaryPairContraction.targetWord
          step.first step.second step.first_ne_second
          (ReductionToken.expand step.tailTokens) :=
    step.expand_targetTokens
  have targetValid :
      (Dyck.oneFace (ReductionToken.expand step.targetTokens)).IsSurfaceValid := by
    rw [htarget]
    exact validTargetWord
  refine
    { targetValid := targetValid
      targetSeparated := step.targetTokens_isSeparated separated
      targetClassified := step.targetTokens_allClassified classified
      targetProtectedNodup :=
        step.targetTokens_protectedNames_nodup protectedNodup
      equivalent := ?_ }
  have hrotation :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (ReductionToken.expand tokens), valid⟩
        ⟨Dyck.oneFace
          (BoundaryPairContraction.sourceWord
            step.first step.second
            step.firstNegative step.secondNegative
            (ReductionToken.expand step.tailTokens)), validSourceWord⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  have hchain := hrotation.trans hequivalentWord
  simpa only [htarget] using hchain

end MarkedBoundaryPairContraction

/-- One certified transition which strictly shortens the protected interval of a lifted residual
pair while preserving the total number of residual darts. -/
structure MarkedResidualPairShortening {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens) where
  /-- The `targetEdgeCount` declaration. -/
  targetEdgeCount : ℕ
  /-- The `targetTokens` declaration. -/
  targetTokens : List (ReductionToken targetEdgeCount)
  /-- The `targetPair` declaration. -/
  targetPair :
    MarkedResidualCancellablePair targetTokens
  targetState : MarkedExecutionState targetTokens
  targetProtectedNonempty :
    ReductionToken.protectedNames targetTokens ≠ []
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens),
        state.valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand targetTokens),
        targetState.valid⟩
  residualLengthEq :
    (ReductionToken.residualDarts targetTokens).length =
      (ReductionToken.residualDarts tokens).length
  rawBoundaryCountTailEq :
    ReductionToken.rawBoundaryCount
        targetPair.tailTokens =
      ReductionToken.rawBoundaryCount pair.tailTokens
  betweenLengthLt :
    targetPair.betweenTokens.length <
      pair.betweenTokens.length

namespace MarkedResidualPairShortening

/-- Prepend a residual- and interval-length-preserving marked transition to a strict shortening. -/
def prepend {n m : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    {middleTokens : List (ReductionToken m)}
    (middlePair :
      MarkedResidualCancellablePair middleTokens)
    (middleState : MarkedExecutionState middleTokens)
    (stepEquivalent :
      NormalizationEquivalent
        ⟨Dyck.oneFace (ReductionToken.expand tokens),
          state.valid⟩
        ⟨Dyck.oneFace
          (ReductionToken.expand middleTokens),
          middleState.valid⟩)
    (residualLengthEq :
      (ReductionToken.residualDarts middleTokens).length =
        (ReductionToken.residualDarts tokens).length)
    (betweenLengthEq :
      middlePair.betweenTokens.length =
        pair.betweenTokens.length)
    (rawBoundaryCountTailEq :
      ReductionToken.rawBoundaryCount
          middlePair.tailTokens =
        ReductionToken.rawBoundaryCount pair.tailTokens)
    (tail :
      MarkedResidualPairShortening middlePair middleState) :
    MarkedResidualPairShortening pair state where
  targetEdgeCount := tail.targetEdgeCount
  targetTokens := tail.targetTokens
  targetPair := tail.targetPair
  targetState := tail.targetState
  targetProtectedNonempty :=
    tail.targetProtectedNonempty
  equivalent := stepEquivalent.trans tail.equivalent
  residualLengthEq :=
    tail.residualLengthEq.trans residualLengthEq
  rawBoundaryCountTailEq :=
    tail.rawBoundaryCountTailEq.trans rawBoundaryCountTailEq
  betweenLengthLt := by
    rw [← betweenLengthEq]
    exact tail.betweenLengthLt

end MarkedResidualPairShortening

/-- One certified transition which preserves both residual length and protected-interval length. -/
structure MarkedResidualPairRotation {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens) where
  /-- The `targetTokens` declaration. -/
  targetTokens : List (ReductionToken n)
  /-- The `targetPair` declaration. -/
  targetPair :
    MarkedResidualCancellablePair targetTokens
  targetState : MarkedExecutionState targetTokens
  targetProtectedNonempty :
    ReductionToken.protectedNames targetTokens ≠ []
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens),
        state.valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand targetTokens),
        targetState.valid⟩
  residualLengthEq :
    (ReductionToken.residualDarts targetTokens).length =
      (ReductionToken.residualDarts tokens).length
  rawBoundaryCountTailEq :
    ReductionToken.rawBoundaryCount
        targetPair.tailTokens =
      ReductionToken.rawBoundaryCount pair.tailTokens
  betweenLengthEq :
    targetPair.betweenTokens.length =
      pair.betweenTokens.length

namespace MarkedResidualCancellablePair

/-- Move a leading raw boundary atom behind a nonempty protected suffix without changing either
the residual or protected-interval measure. -/
noncomputable def rotateBoundaryAtom {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (hole : Fin n) (holeNegative : Bool)
    (insideTokens : List (ReductionToken n))
    (hbetween :
      pair.betweenTokens =
        .extracted (.boundary hole holeNegative) ::
          insideTokens) :
    MarkedResidualPairRotation pair state := by
  cases n with
  | zero =>
      exact Fin.elim0 hole
  | succ k =>
      let step :=
        pair.toBoundaryAtomRotateOfValid hole holeNegative
          insideTokens hbetween state.valid
      have stepInside : step.insideTokens = insideTokens := rfl
      let execution :=
        step.rotate state.separated state.classified
          state.protectedNodup state.valid
      let targetPair := step.targetPair
      refine
        { targetTokens := step.targetTokens
          targetPair := targetPair
          targetState :=
            { valid := execution.targetValid
              separated := execution.targetSeparated
              classified := execution.targetClassified
              protectedNodup :=
                execution.targetProtectedNodup }
          targetProtectedNonempty :=
            ReductionToken.protectedNames_ne_nil_of_perm
              protectedNonempty step.perm_targetTokens
          equivalent := execution.equivalent
          residualLengthEq :=
            ReductionToken.residualDarts_length_of_perm
              step.perm_targetTokens
          rawBoundaryCountTailEq := rfl
          betweenLengthEq := by
            rw [hbetween]
            dsimp [targetPair,
              MarkedBoundaryAtomRotate.targetPair]
            simp [stepInside] }

@[simp]
theorem rotateBoundaryAtom_targetPair_betweenTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (hole : Fin n) (holeNegative : Bool)
    (insideTokens : List (ReductionToken n))
    (hbetween :
      pair.betweenTokens =
        .extracted (.boundary hole holeNegative) ::
          insideTokens) :
    (pair.rotateBoundaryAtom state protectedNonempty
        hole holeNegative insideTokens hbetween).targetPair.betweenTokens =
      insideTokens ++
        [.extracted (.boundary hole holeNegative)] := by
  cases n with
  | zero =>
      exact Fin.elim0 hole
  | succ k =>
      rfl

/-- Commute a completed boundary loop out of a lifted pair, producing a strict interval
shortening. -/
noncomputable def shortenBoundaryBlock {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (carrier hole : Fin (n + 1))
    (carrierNegative holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.boundary carrier hole
          carrierNegative holeNegative) ::
          insideTokens) :
    MarkedResidualPairShortening pair state := by
  have residualInside :
      ReductionToken.residualDarts insideTokens = [] := by
    have h := pair.residual_between
    rw [hbetween] at h
    simpa using h
  let step :=
    pair.toBoundaryBlockCommuteOfValid carrier hole
      carrierNegative holeNegative insideTokens
      hbetween state.valid
  have stepInside : step.insideTokens = insideTokens := by
    exact pair.toBoundaryBlockCommuteOfValid_insideTokens carrier hole
      carrierNegative holeNegative insideTokens hbetween state.valid
  have stepOutside :
      step.outsideTokens = pair.tailTokens := by
    exact pair.toBoundaryBlockCommuteOfValid_outsideTokens carrier hole
      carrierNegative holeNegative insideTokens hbetween state.valid
  let execution :=
    step.commute state.separated state.classified
      state.protectedNodup state.valid
  let targetPair := step.targetPair residualInside
  refine
    { targetEdgeCount := n + 1
      targetTokens := step.targetTokens
      targetPair := targetPair
      targetState :=
        { valid := execution.targetValid
          separated := execution.targetSeparated
          classified := execution.targetClassified
          protectedNodup :=
            execution.targetProtectedNodup }
      targetProtectedNonempty :=
        ReductionToken.protectedNames_ne_nil_of_perm
          protectedNonempty step.perm_targetTokens
      equivalent := execution.equivalent
      residualLengthEq := ?_
      rawBoundaryCountTailEq := by
        dsimp [targetPair,
          MarkedBoundaryBlockCommute.targetPair]
        rw [stepOutside]
        simp [ReductionToken.rawBoundaryCount]
      betweenLengthLt := ?_ }
  · rw [targetPair.residualDarts_length_eq,
      pair.residualDarts_length_eq]
    dsimp [targetPair,
      MarkedBoundaryBlockCommute.targetPair]
    simp [stepOutside]
  · rw [hbetween]
    dsimp [targetPair,
      MarkedBoundaryBlockCommute.targetPair]
    simp [stepInside]

@[simp]
private theorem shortenBoundaryBlock_targetPair_betweenTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ [])
    (carrier hole : Fin (n + 1)) (carrierNegative holeNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.boundary carrier hole carrierNegative holeNegative) :: insideTokens) :
    (pair.shortenBoundaryBlock state protectedNonempty carrier hole carrierNegative holeNegative
      insideTokens hbetween).targetPair.betweenTokens = insideTokens := by
  rfl

/-- Commute a completed crosscap out of a lifted pair, producing a strict interval shortening. -/
noncomputable def shortenCrosscapBlock {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (carrier : Fin (n + 1))
    (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.crosscap carrier
          carrierNegative) ::
          insideTokens) :
    MarkedResidualPairShortening pair state := by
  have residualInside :
      ReductionToken.residualDarts insideTokens = [] := by
    have h := pair.residual_between
    rw [hbetween] at h
    simpa using h
  let step :=
    pair.toCrosscapBlockCommuteOfValid carrier
      carrierNegative insideTokens hbetween state.valid
  have stepInside : step.insideTokens = insideTokens := by
    exact pair.toCrosscapBlockCommuteOfValid_insideTokens carrier carrierNegative
      insideTokens hbetween state.valid
  have stepOutside :
      step.outsideTokens = pair.tailTokens := by
    exact pair.toCrosscapBlockCommuteOfValid_outsideTokens carrier carrierNegative
      insideTokens hbetween state.valid
  let execution :=
    step.commute state.separated state.classified
      state.protectedNodup state.valid
  let targetPair := step.targetPair residualInside
  refine
    { targetEdgeCount := n + 1
      targetTokens := step.targetTokens
      targetPair := targetPair
      targetState :=
        { valid := execution.targetValid
          separated := execution.targetSeparated
          classified := execution.targetClassified
          protectedNodup :=
            execution.targetProtectedNodup }
      targetProtectedNonempty := by
        simp [step, MarkedCrosscapBlockCommute.targetTokens,
          CompletedBlock.names]
      equivalent := execution.equivalent
      residualLengthEq := ?_
      rawBoundaryCountTailEq := by
        dsimp [targetPair,
          MarkedCrosscapBlockCommute.targetPair]
        rw [stepOutside]
        simp [ReductionToken.rawBoundaryCount]
      betweenLengthLt := ?_ }
  · rw [targetPair.residualDarts_length_eq,
      pair.residualDarts_length_eq]
    dsimp [targetPair,
      MarkedCrosscapBlockCommute.targetPair]
    simp [stepOutside, inverseWord_length]
  · rw [hbetween]
    dsimp [targetPair,
      MarkedCrosscapBlockCommute.targetPair]
    simp [stepInside]

@[simp]
private theorem shortenCrosscapBlock_targetPair_betweenTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (carrier : Fin (n + 1)) (carrierNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens = .completed (.crosscap carrier carrierNegative) :: insideTokens) :
    (pair.shortenCrosscapBlock state carrier carrierNegative insideTokens hbetween
      ).targetPair.betweenTokens = insideTokens := by
  rfl

/-- Commute a completed handle out of a lifted pair, producing a strict interval shortening. -/
noncomputable def shortenHandleBlock {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .completed (.handle first second) ::
          insideTokens) :
    MarkedResidualPairShortening pair state := by
  have residualInside :
      ReductionToken.residualDarts insideTokens = [] := by
    have h := pair.residual_between
    rw [hbetween] at h
    simpa using h
  let step :=
    pair.toHandleBlockCommuteOfValid first second
      insideTokens hbetween state.valid
  have stepInside : step.insideTokens = insideTokens := by
    exact pair.toHandleBlockCommuteOfValid_insideTokens first second insideTokens
      hbetween state.valid
  have stepOutside :
      step.outsideTokens = pair.tailTokens := by
    exact pair.toHandleBlockCommuteOfValid_outsideTokens first second insideTokens
      hbetween state.valid
  let execution :=
    step.commute state.separated state.classified
      state.protectedNodup state.valid
  let targetPair := step.targetPair residualInside
  refine
    { targetEdgeCount := n + 1
      targetTokens := step.targetTokens
      targetPair := targetPair
      targetState :=
        { valid := execution.targetValid
          separated := execution.targetSeparated
          classified := execution.targetClassified
          protectedNodup :=
            execution.targetProtectedNodup }
      targetProtectedNonempty :=
        ReductionToken.protectedNames_ne_nil_of_perm
          protectedNonempty step.perm_targetTokens
      equivalent := execution.equivalent
      residualLengthEq := ?_
      rawBoundaryCountTailEq := by
        dsimp [targetPair,
          MarkedHandleBlockCommute.targetPair]
        rw [stepOutside]
        simp [ReductionToken.rawBoundaryCount]
      betweenLengthLt := ?_ }
  · rw [targetPair.residualDarts_length_eq,
      pair.residualDarts_length_eq]
    dsimp [targetPair,
      MarkedHandleBlockCommute.targetPair]
    simp [stepOutside]
  · rw [hbetween]
    dsimp [targetPair,
      MarkedHandleBlockCommute.targetPair]
    simp [stepInside]

@[simp]
private theorem shortenHandleBlock_targetPair_betweenTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ [])
    (first second : Fin (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween : pair.betweenTokens = .completed (.handle first second) :: insideTokens) :
    (pair.shortenHandleBlock state protectedNonempty first second insideTokens hbetween
      ).targetPair.betweenTokens = insideTokens := by
  rfl

/-- Contract two adjacent raw boundary atoms, producing a strict interval shortening in the
lowered ambient edge type. -/
noncomputable def shortenBoundaryPair {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++
          insideTokens) :
    MarkedResidualPairShortening pair state := by
  let step :=
    pair.toBoundaryPairContraction first second
      firstNegative secondNegative insideTokens hbetween
      state.separated state.protectedNodup
  let execution :=
    step.contract state.separated state.classified
      state.protectedNodup state.valid
  let targetPair :=
    pair.boundaryContractionTargetPair first second
      firstNegative secondNegative insideTokens hbetween
      state.separated state.protectedNodup
  refine
    { targetEdgeCount := n
      targetTokens := step.targetTokens
      targetPair := targetPair
      targetState :=
        { valid := execution.targetValid
          separated := execution.targetSeparated
          classified := execution.targetClassified
          protectedNodup :=
            execution.targetProtectedNodup }
      targetProtectedNonempty := by
        simp [step,
          MarkedBoundaryPairContraction.targetTokens,
          ExtractedBlock.edges]
      equivalent := execution.equivalent
      residualLengthEq :=
        step.residualDarts_targetTokens_length_eq
      rawBoundaryCountTailEq := by
        change
          ReductionToken.rawBoundaryCount
              (ReductionToken.lowerTokensAvoiding second
                pair.tailTokens _) =
            ReductionToken.rawBoundaryCount pair.tailTokens
        exact
          ReductionToken.rawBoundaryCount_lowerTokensAvoiding
            second pair.tailTokens _
      betweenLengthLt :=
        pair.boundaryContractionTargetPair_between_length_lt
          first second firstNegative secondNegative
          insideTokens hbetween state.separated
          state.protectedNodup }

private theorem shortenBoundaryPair_targetPair_betweenTokens_length {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (first second : Fin (n + 1)) (firstNegative secondNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++ insideTokens) :
    (pair.shortenBoundaryPair state first second firstNegative secondNegative insideTokens
      hbetween).targetPair.betweenTokens.length = insideTokens.length + 1 := by
  simp [shortenBoundaryPair, boundaryContractionTargetPair]

@[simp]
private theorem shortenBoundaryPair_targetPair_betweenTokens {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (first second : Fin (n + 1)) (firstNegative secondNegative : Bool)
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary first firstNegative),
          .extracted (.boundary second secondNegative)] ++ insideTokens) :
    let step := pair.toBoundaryPairContraction first second firstNegative secondNegative
      insideTokens hbetween state.separated state.protectedNodup
    let loweredInside := ReductionToken.lowerTokensAvoiding second insideTokens (by
      intro hmem
      apply step.second_not_mem_tail
      change second ∈
        (ReductionToken.expand
          (insideTokens ++
            .residual (dart pair.edge (!pair.negativeFirst)) ::
              pair.tailTokens ++ [.residual (dart pair.edge pair.negativeFirst)])).map edgeOfDart
      simp [hmem])
    (pair.shortenBoundaryPair state first second firstNegative secondNegative insideTokens
      hbetween).targetPair.betweenTokens =
        .extracted
            (.boundary
              (Cancellation.lowerEdge second first step.first_ne_second) false) ::
          loweredInside := by
  rfl

private noncomputable def shortenCompletedBlock {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ [])
    (block : CompletedBlock (n + 1))
    (insideTokens : List (ReductionToken (n + 1)))
    (hbetween : pair.betweenTokens = .completed block :: insideTokens) :
    MarkedResidualPairShortening pair state := by
  cases block with
  | boundary carrier hole carrierNegative holeNegative =>
      exact pair.shortenBoundaryBlock state protectedNonempty carrier hole carrierNegative
        holeNegative insideTokens hbetween
  | crosscap carrier carrierNegative =>
      exact pair.shortenCrosscapBlock state carrier carrierNegative insideTokens hbetween
  | handle first second =>
      exact pair.shortenHandleBlock state protectedNonempty first second insideTokens hbetween

private noncomputable def shortenBoundaryThenCompletedBlock {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ [])
    (hole : Fin (n + 1)) (holeNegative : Bool)
    (block : CompletedBlock (n + 1))
    (remainingTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .extracted (.boundary hole holeNegative) :: .completed block :: remainingTokens) :
    MarkedResidualPairShortening pair state := by
  let insideTokens := .completed block :: remainingTokens
  have hrotate :
      pair.betweenTokens = .extracted (.boundary hole holeNegative) :: insideTokens := by
    exact hbetween
  let rotation :=
    pair.rotateBoundaryAtom state protectedNonempty hole holeNegative insideTokens hrotate
  let rotatedInsideTokens :=
    remainingTokens ++
      [(.extracted (.boundary hole holeNegative) : ReductionToken (n + 1))]
  have hrotationBetween :
      rotation.targetPair.betweenTokens = .completed block :: rotatedInsideTokens := by
    calc
      rotation.targetPair.betweenTokens =
          insideTokens ++ [.extracted (.boundary hole holeNegative)] :=
        pair.rotateBoundaryAtom_targetPair_betweenTokens state protectedNonempty hole
          holeNegative insideTokens hrotate
      _ = .completed block :: rotatedInsideTokens := by
        simp [insideTokens, rotatedInsideTokens]
  let shorteningAfter :=
    shortenCompletedBlock rotation.targetPair rotation.targetState
      rotation.targetProtectedNonempty block rotatedInsideTokens hrotationBetween
  exact MarkedResidualPairShortening.prepend pair state rotation.targetPair rotation.targetState
    rotation.equivalent rotation.residualLengthEq rotation.betweenLengthEq
    rotation.rawBoundaryCountTailEq shorteningAfter

private theorem shortenBoundaryThenCompletedBlock_betweenLengthLt {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ [])
    (hole : Fin (n + 1)) (holeNegative : Bool)
    (block : CompletedBlock (n + 1))
    (remainingTokens : List (ReductionToken (n + 1)))
    (hbetween :
      pair.betweenTokens =
        .extracted (.boundary hole holeNegative) :: .completed block :: remainingTokens) :
    (shortenBoundaryThenCompletedBlock pair state protectedNonempty hole holeNegative block
      remainingTokens hbetween).targetPair.betweenTokens.length < pair.betweenTokens.length :=
  (shortenBoundaryThenCompletedBlock pair state protectedNonempty hole holeNegative block
    remainingTokens hbetween).betweenLengthLt

end MarkedResidualCancellablePair

/-- Certified elimination of one lifted residual inverse pair.  The target may have a smaller
ambient edge type after P1 cancellation or boundary contraction, but always has strictly fewer
residual darts and retains at least one protected name. -/
structure MarkedResidualPairResolution {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens) where
  /-- The `targetEdgeCount` declaration. -/
  targetEdgeCount : ℕ
  /-- The `targetTokens` declaration. -/
  targetTokens : List (ReductionToken targetEdgeCount)
  targetState : MarkedExecutionState targetTokens
  targetProtectedNonempty :
    ReductionToken.protectedNames targetTokens ≠ []
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens),
        state.valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand targetTokens),
        targetState.valid⟩
  residualLengthEqTail :
    (ReductionToken.residualDarts targetTokens).length =
      (ReductionToken.residualDarts pair.tailTokens).length
  rawBoundaryCountEqTail :
    ReductionToken.rawBoundaryCount targetTokens =
      ReductionToken.rawBoundaryCount pair.tailTokens
  residualLengthLt :
    (ReductionToken.residualDarts targetTokens).length <
      (ReductionToken.residualDarts tokens).length

namespace MarkedResidualPairResolution

/-- Prepend a residual-length-preserving marked transition to a completed pair resolution. -/
def prepend {n m : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    {middleTokens : List (ReductionToken m)}
    (middlePair :
      MarkedResidualCancellablePair middleTokens)
    (middleState : MarkedExecutionState middleTokens)
    (stepEquivalent :
      NormalizationEquivalent
        ⟨Dyck.oneFace (ReductionToken.expand tokens),
          state.valid⟩
        ⟨Dyck.oneFace
          (ReductionToken.expand middleTokens),
          middleState.valid⟩)
    (residualLengthEq :
      (ReductionToken.residualDarts middleTokens).length =
        (ReductionToken.residualDarts tokens).length)
    (rawBoundaryCountTailEq :
      ReductionToken.rawBoundaryCount
          middlePair.tailTokens =
        ReductionToken.rawBoundaryCount pair.tailTokens)
    (tail :
      MarkedResidualPairResolution middlePair middleState) :
    MarkedResidualPairResolution pair state where
  targetEdgeCount := tail.targetEdgeCount
  targetTokens := tail.targetTokens
  targetState := tail.targetState
  targetProtectedNonempty :=
    tail.targetProtectedNonempty
  equivalent := stepEquivalent.trans tail.equivalent
  residualLengthEqTail := by
    rw [tail.residualLengthEqTail]
    have hsource := pair.residualDarts_length_eq
    have hmiddle := middlePair.residualDarts_length_eq
    omega
  rawBoundaryCountEqTail :=
    tail.rawBoundaryCountEqTail.trans rawBoundaryCountTailEq
  residualLengthLt := by
    rw [← residualLengthEq]
    exact tail.residualLengthLt

end MarkedResidualPairResolution

private theorem resolution_rawBoundaryCount_eq_tail {n : ℕ}
    {tokens : List (ReductionToken n)}
    {pair : MarkedResidualCancellablePair tokens}
    {state : MarkedExecutionState tokens}
    (resolution : MarkedResidualPairResolution pair state) :
    ReductionToken.rawBoundaryCount resolution.targetTokens =
      ReductionToken.rawBoundaryCount pair.tailTokens :=
  resolution.rawBoundaryCountEqTail

namespace MarkedResidualCancellablePair

/-- Eliminate an adjacent lifted pair by ordinary cancellation.  A protected-name witness rules
out the exceptional empty-tail sphere endpoint. -/
noncomputable def resolveAdjacent {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (hempty : pair.betweenTokens = []) :
    MarkedResidualPairResolution pair state := by
  cases n with
  | zero =>
      exact Fin.elim0 pair.edge
  | succ k =>
      let adjacent := pair.toAdjacent hempty
      have tailProtectedNonempty :
          ReductionToken.protectedNames
              adjacent.tailTokens ≠ [] := by
        have hlength :=
          (ReductionToken.protectedNames_isRotated
            adjacent.rotated).perm.length_eq
        have hlength' :
            (ReductionToken.protectedNames tokens).length =
              (ReductionToken.protectedNames
                adjacent.tailTokens).length := by
          simpa using hlength
        intro htail
        apply protectedNonempty
        apply List.length_eq_zero_iff.mp
        rw [hlength', htail]
        rfl
      have tail_nonempty :
          ReductionToken.expand adjacent.tailTokens ≠ [] := by
        intro hexpand
        cases hnames :
            ReductionToken.protectedNames
              adjacent.tailTokens with
        | nil =>
            exact tailProtectedNonempty hnames
        | cons edge edges =>
            have hedgeNames :
                edge ∈
                  ReductionToken.protectedNames
                    adjacent.tailTokens := by
              simp [hnames]
            have hedgeProtected :
                edge ∈
                  ReductionToken.protectedEdges
                    adjacent.tailTokens :=
              (ReductionToken.mem_protectedNames_iff_mem_protectedEdges
                adjacent.tailTokens edge).mp hedgeNames
            have hedgeExpand :
                edge ∈
                  (ReductionToken.expand
                    adjacent.tailTokens).map edgeOfDart :=
              (ReductionToken.mem_map_edgeOfDart_expand_iff
                adjacent.tailTokens edge).mpr
                  (Or.inr hedgeProtected)
            simp [hexpand] at hedgeExpand
      let execution :=
        adjacent.cancel state.separated state.classified
          state.protectedNodup state.valid tail_nonempty
      let targetTokens :=
        adjacent.cancellationTargetTokens state.valid
      have targetProtectedNonempty :
          ReductionToken.protectedNames targetTokens ≠ [] := by
        intro htarget
        have hrestore :=
          ReductionToken.protectedNames_lowerTokensAvoiding_map_restoreEdge
            adjacent.edge adjacent.tailTokens
              (adjacent.edge_not_mem_tailTokens state.valid)
        change
          (ReductionToken.protectedNames targetTokens).map
              (Cancellation.restoreEdge adjacent.edge) =
            ReductionToken.protectedNames
              adjacent.tailTokens at hrestore
        rw [htarget] at hrestore
        exact tailProtectedNonempty (by simpa using hrestore.symm)
      have hrestore :=
        ReductionToken.residualEdges_lowerTokensAvoiding_map_restoreEdge
          adjacent.edge adjacent.tailTokens
            (adjacent.edge_not_mem_tailTokens state.valid)
      have htargetLength :
          (ReductionToken.residualDarts targetTokens).length =
            (ReductionToken.residualDarts
              pair.tailTokens).length := by
        have hlength := congrArg List.length hrestore
        have hlowered :
            (ReductionToken.residualDarts targetTokens).length =
              (ReductionToken.residualDarts
                adjacent.tailTokens).length := by
          simpa [targetTokens,
            MarkedCancellablePair.cancellationTargetTokens] using
              hlength
        exact hlowered
      refine
        { targetEdgeCount := k
          targetTokens := targetTokens
          targetState :=
            { valid := execution.targetValid
              separated := execution.targetSeparated
              classified := execution.targetClassified
              protectedNodup :=
                execution.targetProtectedNodup }
          targetProtectedNonempty := targetProtectedNonempty
          equivalent := execution.equivalent
          residualLengthEqTail := htargetLength
          rawBoundaryCountEqTail := by
            change
              ReductionToken.rawBoundaryCount
                  (ReductionToken.lowerTokensAvoiding
                    pair.edge pair.tailTokens _) =
                ReductionToken.rawBoundaryCount pair.tailTokens
            exact
              ReductionToken.rawBoundaryCount_lowerTokensAvoiding
                pair.edge pair.tailTokens _
          residualLengthLt := ?_ }
      rw [htargetLength, pair.residualDarts_length_eq]
      omega

private theorem resolveAdjacent_rawBoundaryCount_eq_tail {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ [])
    (hempty : pair.betweenTokens = []) :
    ReductionToken.rawBoundaryCount
        (pair.resolveAdjacent state protectedNonempty hempty).targetTokens =
      ReductionToken.rawBoundaryCount pair.tailTokens :=
  resolution_rawBoundaryCount_eq_tail (pair.resolveAdjacent state protectedNonempty hempty)

/-- Eliminate a lifted pair surrounding one raw boundary atom by reclassifying the three displayed
tokens as one completed boundary loop. -/
noncomputable def resolveBoundary {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (hole : Fin (n + 1)) (holeNegative : Bool)
    (hbetween :
      pair.betweenTokens =
        [.extracted (.boundary hole holeNegative)]) :
    MarkedResidualPairResolution pair state := by
  let closure :=
    pair.toBoundaryClosure hole holeNegative hbetween
  let execution :=
    closure.close state.separated state.classified
      state.protectedNodup state.valid
  refine
    { targetEdgeCount := n + 1
      targetTokens := closure.targetTokens
      targetState :=
        { valid := execution.targetValid
          separated := execution.targetSeparated
          classified := execution.targetClassified
          protectedNodup :=
            execution.targetProtectedNodup }
      targetProtectedNonempty := by
        simp [closure, MarkedBoundaryClosure.targetTokens,
          CompletedBlock.names]
      equivalent := execution.equivalent
      residualLengthEqTail := by
        simp [closure, MarkedBoundaryClosure.targetTokens,
          MarkedResidualCancellablePair.toBoundaryClosure]
      rawBoundaryCountEqTail := by
        simp [closure, MarkedBoundaryClosure.targetTokens,
          MarkedResidualCancellablePair.toBoundaryClosure,
          ReductionToken.rawBoundaryCount]
      residualLengthLt := ?_ }
  rw [pair.residualDarts_length_eq]
  simp [closure, MarkedBoundaryClosure.targetTokens,
    MarkedResidualCancellablePair.toBoundaryClosure]

private theorem resolveBoundary_rawBoundaryCount_eq_tail {n : ℕ}
    {tokens : List (ReductionToken (n + 1))}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (hole : Fin (n + 1)) (holeNegative : Bool)
    (hbetween : pair.betweenTokens = [.extracted (.boundary hole holeNegative)]) :
    ReductionToken.rawBoundaryCount
        (pair.resolveBoundary state hole holeNegative hbetween).targetTokens =
      ReductionToken.rawBoundaryCount pair.tailTokens :=
  resolution_rawBoundaryCount_eq_tail (pair.resolveBoundary state hole holeNegative hbetween)

private inductive CertifiedResolutionStep {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens) : Type
  | resolved (resolution : MarkedResidualPairResolution pair state)
  | shortened (shortening : MarkedResidualPairShortening pair state)

private noncomputable def nextResolutionStep {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ []) :
    CertifiedResolutionStep pair state := by
  cases n with
  | zero => exact Fin.elim0 pair.edge
  | succ k =>
      cases pair.classifiedDisposition state.classified with
      | adjacent hempty =>
          exact .resolved (pair.resolveAdjacent state protectedNonempty hempty)
      | boundary hole holeNegative hbetween =>
          exact .resolved (pair.resolveBoundary state hole holeNegative hbetween)
      | structured first rest hbetween =>
          cases first with
          | completed block =>
              let insideTokens := rest.map ReductionToken.ofProtectedAtom
              have hbetween' : pair.betweenTokens = .completed block :: insideTokens := by
                simpa [insideTokens, ReductionToken.ofProtectedAtom] using hbetween
              exact .shortened
                (shortenCompletedBlock pair state protectedNonempty block insideTokens hbetween')
          | boundary hole holeNegative =>
              cases rest with
              | nil =>
                  exact .resolved (pair.resolveBoundary state hole holeNegative (by
                    simpa [ReductionToken.ofProtectedAtom] using hbetween))
              | cons second restTail =>
                  let remainingTokens := restTail.map ReductionToken.ofProtectedAtom
                  cases second with
                  | boundary secondHole secondNegative =>
                      have hbetween' :
                          pair.betweenTokens =
                            [.extracted (.boundary hole holeNegative),
                              .extracted (.boundary secondHole secondNegative)] ++
                              remainingTokens := by
                        simpa [remainingTokens, ReductionToken.ofProtectedAtom] using hbetween
                      exact .shortened
                        (pair.shortenBoundaryPair state hole secondHole holeNegative secondNegative
                          remainingTokens hbetween')
                  | completed block =>
                      have hbetween' :
                          pair.betweenTokens =
                            .extracted (.boundary hole holeNegative) ::
                              .completed block :: remainingTokens := by
                        simpa [remainingTokens, ReductionToken.ofProtectedAtom] using hbetween
                      exact .shortened
                        (shortenBoundaryThenCompletedBlock pair state protectedNonempty hole
                          holeNegative block remainingTokens hbetween')

private theorem nextResolutionStep_shortening_decreases {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty : ReductionToken.protectedNames tokens ≠ []) :
    match nextResolutionStep pair state protectedNonempty with
    | .resolved _ => True
    | .shortened shortening =>
        shortening.targetPair.betweenTokens.length < pair.betweenTokens.length := by
  cases nextResolutionStep pair state protectedNonempty with
  | resolved => trivial
  | shortened shortening => exact shortening.betweenLengthLt

private def finishShorteningResolution {n : ℕ}
    {tokens : List (ReductionToken n)}
    {pair : MarkedResidualCancellablePair tokens}
    {state : MarkedExecutionState tokens}
    (shortening : MarkedResidualPairShortening pair state)
    (tail : MarkedResidualPairResolution shortening.targetPair shortening.targetState) :
    MarkedResidualPairResolution pair state :=
  MarkedResidualPairResolution.prepend pair state shortening.targetPair shortening.targetState
    shortening.equivalent shortening.residualLengthEq shortening.rawBoundaryCountTailEq tail

/-- Resolve one lifted residual inverse pair.  The fuel measures the protected interval: every
contextual step strictly shortens it, while the terminal cases eliminate the residual pair. -/
noncomputable def resolveFuel {n : ℕ}
    {tokens : List (ReductionToken n)}
    (fuel : ℕ)
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (hbound : pair.betweenTokens.length ≤ fuel) :
    MarkedResidualPairResolution pair state := by
  cases nextResolutionStep pair state protectedNonempty with
  | resolved resolution => exact resolution
  | shortened shortening =>
      have hfuelPositive : 0 < fuel := by
        have hshort := shortening.betweenLengthLt
        omega
      have htargetBound :
          shortening.targetPair.betweenTokens.length ≤ fuel - 1 := by
        have hshort := shortening.betweenLengthLt
        omega
      exact finishShorteningResolution shortening
        (resolveFuel (fuel - 1) shortening.targetPair shortening.targetState
          shortening.targetProtectedNonempty htargetBound)
termination_by fuel
decreasing_by
  apply Nat.sub_lt
  · exact hfuelPositive
  · omega

/-- Eliminate one lifted residual inverse pair by the terminating protected-interval resolver. -/
noncomputable def resolve {n : ℕ}
    {tokens : List (ReductionToken n)}
    (pair : MarkedResidualCancellablePair tokens)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ []) :
    MarkedResidualPairResolution pair state :=
  resolveFuel pair.betweenTokens.length pair state
    protectedNonempty (le_refl _)

end MarkedResidualCancellablePair

/-- Certified marked endpoint after all cancellable pairs have been removed from the erased
residual word.  Already protected names remain present, even when cancellations lower the ambient
edge type. -/
structure MarkedPairReductionResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (state : MarkedExecutionState tokens) where
  /-- The `targetEdgeCount` declaration. -/
  targetEdgeCount : ℕ
  /-- The `targetTokens` declaration. -/
  targetTokens : List (ReductionToken targetEdgeCount)
  targetState : MarkedExecutionState targetTokens
  targetProtectedNonempty :
    ReductionToken.protectedNames targetTokens ≠ []
  targetReduced :
    IsPairReduced (ReductionToken.residualDarts targetTokens)
  targetResidualLengthLe :
    (ReductionToken.residualDarts targetTokens).length ≤
      (ReductionToken.residualDarts tokens).length
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens),
        state.valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand targetTokens),
        targetState.valid⟩

namespace MarkedExecutionState

/-- Fuel-bounded execution of residual inverse-pair reduction inside a classified marked word.
Each resolved pair strictly decreases the erased residual length. -/
noncomputable def reduceResidualPairsFuel {n : ℕ}
    {tokens : List (ReductionToken n)}
    (fuel : ℕ)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (hbound :
      (ReductionToken.residualDarts tokens).length ≤ fuel) :
    MarkedPairReductionResult state := by
  by_cases hpairs :
      Nonempty
        (CancellablePair
          (ReductionToken.residualDarts tokens))
  · cases n with
    | zero =>
        let pair := Classical.choice hpairs
        exact Fin.elim0 pair.edge
    | succ k =>
        let residualPair := Classical.choice hpairs
        let markedPair :=
          MarkedResidualCancellablePair.lift residualPair
        let resolution :=
          markedPair.resolve state protectedNonempty
        have hfuelPositive : 0 < fuel := by
          have := resolution.residualLengthLt
          omega
        have htargetBound :
            (ReductionToken.residualDarts
                resolution.targetTokens).length ≤
              fuel - 1 := by
          have := resolution.residualLengthLt
          omega
        let tail :=
          reduceResidualPairsFuel (fuel - 1)
            resolution.targetState
            resolution.targetProtectedNonempty htargetBound
        exact
          { targetEdgeCount := tail.targetEdgeCount
            targetTokens := tail.targetTokens
            targetState := tail.targetState
            targetProtectedNonempty :=
              tail.targetProtectedNonempty
            targetReduced := tail.targetReduced
            targetResidualLengthLe := by
              have htail := tail.targetResidualLengthLe
              have hstep := resolution.residualLengthLt
              omega
            equivalent :=
              resolution.equivalent.trans tail.equivalent }
  · exact
      { targetEdgeCount := n
        targetTokens := tokens
        targetState := state
        targetProtectedNonempty := protectedNonempty
        targetReduced :=
          ⟨fun pair => hpairs ⟨pair⟩⟩
        targetResidualLengthLe := le_rfl
        equivalent := NormalizationEquivalent.refl _ }
termination_by fuel
decreasing_by
  all_goals
    exact Nat.sub_lt (by assumption) (by omega)

/-- Execute all residual inverse-pair cancellations in a marked state which already owns at least
one protected name. -/
noncomputable def reduceResidualPairs {n : ℕ}
    {tokens : List (ReductionToken n)}
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ []) :
    MarkedPairReductionResult state :=
  reduceResidualPairsFuel
    (ReductionToken.residualDarts tokens).length
    state protectedNonempty (le_refl _)

end MarkedExecutionState

/-- The local feature exposed at a selected edge of a pair-reduced valid word. -/
inductive PairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
  | boundary (a : Fin n) (form : BoundaryOccurrenceForm word a)
  | crosscap (a : Fin n) (form : CrosscapOccurrenceForm word a)
  | opposite (a : Fin n) (form : OppositeOccurrenceForm word a)
      (between_nonempty : form.between ≠ [])

/-- Every pair-reduced valid word with at least one edge exposes either a boundary dart, an
equally oriented crosscap pair, or a nondegenerate opposite pair. -/
theorem exists_pairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word)
    (hn : 0 < n) :
    Nonempty (PairReductionFeature word) := by
  let a : Fin n := ⟨0, hn⟩
  let pattern := Classical.choice (exists_edgePattern word valid a)
  cases pattern with
  | boundary hcount =>
      let form :=
        Classical.choice
          (exists_boundaryOccurrenceForm word a hcount)
      exact ⟨.boundary a form⟩
  | positiveCrosscap hpositive hnegative =>
      let form :=
        Classical.choice
          (exists_positiveCrosscapOccurrenceForm
            word a hpositive hnegative)
      exact ⟨.crosscap a form⟩
  | negativeCrosscap hpositive hnegative =>
      let form :=
        Classical.choice
          (exists_negativeCrosscapOccurrenceForm
            word a hpositive hnegative)
      exact ⟨.crosscap a form⟩
  | opposite hpositive hnegative =>
      let form :=
        Classical.choice
          (exists_oppositeOccurrenceForm
            word a hpositive hnegative)
      exact ⟨.opposite a form (form.between_ne_nil reduced)⟩

/-- Every nonempty pair-reduced valid word exposes a feature with a complete local normalization
chain: a boundary edge, a crosscap pair, or an interleaved pair ready for handle extraction. -/
theorem exists_actionablePairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word)
    (hn : 0 < n) :
    Nonempty (ActionablePairReductionFeature word) := by
  let feature :=
    Classical.choice
      (exists_pairReductionFeature word valid reduced hn)
  cases feature with
  | boundary a form =>
      exact ⟨.boundary a form⟩
  | crosscap a form =>
      exact ⟨.crosscap a form⟩
  | opposite a form _ =>
      exact ⟨form.toArc.findActionable valid reduced⟩

/-- Residual form of actionable-feature existence.  It needs only a nonempty residual word,
surface multiplicities for names still used there, and pair reduction; already-grouped ambient
edge names may be absent. -/
theorem exists_actionablePairReductionFeature_of_usedMultiplicities {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word)
    (hne : word ≠ []) :
    Nonempty (ActionablePairReductionFeature word) := by
  cases word with
  | nil =>
      exact (hne rfl).elim
  | cons d tail =>
      let a : Fin n := edgeOfDart d
      have ha : a ∈ (d :: tail).map edgeOfDart := by
        simp [a]
      let pattern :=
        Classical.choice
          (exists_edgePattern_of_multiplicity
            (d :: tail) a (multiplicities a ha))
      cases pattern with
      | boundary hcount =>
          let form :=
            Classical.choice
              (exists_boundaryOccurrenceForm (d :: tail) a hcount)
          exact ⟨.boundary a form⟩
      | positiveCrosscap hpositive hnegative =>
          let form :=
            Classical.choice
              (exists_positiveCrosscapOccurrenceForm
                (d :: tail) a hpositive hnegative)
          exact ⟨.crosscap a form⟩
      | negativeCrosscap hpositive hnegative =>
          let form :=
            Classical.choice
              (exists_negativeCrosscapOccurrenceForm
                (d :: tail) a hpositive hnegative)
          exact ⟨.crosscap a form⟩
      | opposite hpositive hnegative =>
          let form :=
            Classical.choice
              (exists_oppositeOccurrenceForm
                (d :: tail) a hpositive hnegative)
          exact ⟨form.toArc.findActionableOfUsedMultiplicities
            multiplicities reduced⟩

/-- Fuel-bounded decomposition of a pair-reduced residual word into boundary, crosscap, and handle
blocks.  Pair cancellation after each extraction restores the induction hypothesis. -/
noncomputable def decomposeResidualFuel (fuel : ℕ) {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    word.length ≤ fuel → ResidualDecomposition word := by
  classical
  intro hbound
  by_cases hnil : word = []
  · subst word
    exact .done
  · let feature :=
      Classical.choice
        (exists_actionablePairReductionFeature_of_usedMultiplicities
          word multiplicities reduced hnil)
    let residualMultiplicities :=
      feature.hasValidUsedMultiplicities_residualWord
        multiplicities
    let reduction :=
      reduceResidualPairs feature.residualWord
        residualMultiplicities
    have hshort :
        reduction.reducedWord.length < word.length :=
      reduction.length_le.trans_lt feature.residualWord_length_lt
    have hfuelPositive : 0 < fuel := by
      omega
    have htailBound :
        reduction.reducedWord.length ≤ fuel - 1 := by
      omega
    exact .step feature reduction
      (decomposeResidualFuel (fuel - 1)
        reduction.reducedWord reduction.multiplicities
        reduction.reduced htailBound)
termination_by fuel
decreasing_by
  apply Nat.sub_lt
  · exact hfuelPositive
  · omega

/-- Every pair-reduced residual word with valid used-edge multiplicities admits a terminating
block decomposition. -/
noncomputable def decomposeResidual {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    ResidualDecomposition word :=
  decomposeResidualFuel word.length word multiplicities
    reduced (le_refl _)

/-- Surface-valid pair-reduced one-face words admit the residual block decomposition needed by the
global Gallier--Xu normalization recursion. -/
noncomputable def decomposePairReduced {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    ResidualDecomposition word :=
  decomposeResidual word
    (hasValidUsedMultiplicities_of_isSurfaceValid word valid)
    reduced

/-- Normal-form parameters computed from the certified decomposition of a pair-reduced valid
one-face word. -/
noncomputable def pairReducedNormalForm {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) : NormalForm :=
  (decomposePairReduced word valid reduced).normalForm

/-- The normal-form parameters selected from a pair-reduced valid word satisfy the exact
Lean-Eval admissibility predicate. -/
theorem pairReducedNormalForm_isEvalAdmissible {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    (pairReducedNormalForm word valid reduced).IsEvalAdmissible := by
  apply (decomposePairReduced word valid reduced).normalForm_isEvalAdmissible_of_word_ne_nil
  simpa only [Dyck.oneFace_boundary] using
    valid.2.1 (0 : (Dyck.oneFace word).Face)

/-- Find and execute one certified normalization step on any nonempty pair-reduced valid word. -/
noncomputable def extractPairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word)
    (hn : 0 < n) :
    ActionablePairReductionResult word valid :=
  (Classical.choice (exists_actionablePairReductionFeature word valid reduced hn)).extract valid

/-- Certified endpoint of the marked extraction recursion: no residual darts remain, every token
is classified, and at least one protected name survives. -/
structure MarkedExtractionResult {n : ℕ}
    {tokens : List (ReductionToken n)}
    (state : MarkedExecutionState tokens) where
  /-- The `targetEdgeCount` declaration. -/
  targetEdgeCount : ℕ
  /-- The `targetTokens` declaration. -/
  targetTokens : List (ReductionToken targetEdgeCount)
  targetState : MarkedExecutionState targetTokens
  targetProtectedNonempty :
    ReductionToken.protectedNames targetTokens ≠ []
  targetResidualEmpty :
    ReductionToken.residualDarts targetTokens = []
  equivalent :
    NormalizationEquivalent
      ⟨Dyck.oneFace (ReductionToken.expand tokens),
        state.valid⟩
      ⟨Dyck.oneFace
        (ReductionToken.expand targetTokens),
        targetState.valid⟩

namespace MarkedExecutionState

/-- Fuel-bounded marked Gallier--Xu extraction after at least one protected block has been created.
Every extraction strictly shortens the residual word, and the intervening marked pair reducer
restores pair reduction before the recursive call. -/
noncomputable def finishExtractionsFuel {n : ℕ}
    {tokens : List (ReductionToken n)}
    (fuel : ℕ)
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (reduced :
      IsPairReduced (ReductionToken.residualDarts tokens))
    (hbound :
      (ReductionToken.residualDarts tokens).length ≤ fuel) :
    MarkedExtractionResult state := by
  by_cases hresidual :
      ReductionToken.residualDarts tokens = []
  · exact
      { targetEdgeCount := n
        targetTokens := tokens
        targetState := state
        targetProtectedNonempty := protectedNonempty
        targetResidualEmpty := hresidual
        equivalent := NormalizationEquivalent.refl _ }
  · let feature :=
      Classical.choice
        (exists_actionablePairReductionFeature_of_usedMultiplicities
          (ReductionToken.residualDarts tokens)
          state.hasValidUsedMultiplicities_residualDarts
          reduced hresidual)
    let marked :=
      MarkedActionablePairReductionFeature.lift feature
    have hmarkedFeature :
        marked.residualFeature = feature := by
      dsimp [marked]
      cases feature <;> rfl
    let execution :=
      marked.extract state.separated state.classified
        state.protectedNodup state.valid
    let extractedState :
        MarkedExecutionState marked.targetTokens :=
      { valid := execution.targetValid
        separated := execution.targetSeparated
        classified := execution.targetClassified
        protectedNodup :=
          execution.targetProtectedNodup }
    have extractedProtectedNonempty :
        ReductionToken.protectedNames
            marked.targetTokens ≠ [] :=
      marked.protectedNames_targetTokens_ne_nil
    let reduction :=
      extractedState.reduceResidualPairs
        extractedProtectedNonempty
    have hextractionShort :
        (ReductionToken.residualDarts
            marked.targetTokens).length <
          (ReductionToken.residualDarts tokens).length := by
      rw [marked.residualDarts_targetTokens, hmarkedFeature]
      exact feature.residualWord_length_lt
    have hnextShort :
        (ReductionToken.residualDarts
            reduction.targetTokens).length <
          (ReductionToken.residualDarts tokens).length :=
      reduction.targetResidualLengthLe.trans_lt
        hextractionShort
    have hfuelPositive : 0 < fuel := by
      omega
    have htargetBound :
        (ReductionToken.residualDarts
            reduction.targetTokens).length ≤
          fuel - 1 := by
      omega
    let tail :=
      finishExtractionsFuel (fuel - 1)
        reduction.targetState
        reduction.targetProtectedNonempty
        reduction.targetReduced htargetBound
    exact
      { targetEdgeCount := tail.targetEdgeCount
        targetTokens := tail.targetTokens
        targetState := tail.targetState
        targetProtectedNonempty :=
          tail.targetProtectedNonempty
        targetResidualEmpty := tail.targetResidualEmpty
        equivalent :=
          execution.equivalent.trans
            (reduction.equivalent.trans tail.equivalent) }
termination_by fuel
decreasing_by
  exact Nat.sub_lt hfuelPositive (by omega)

/-- Finish marked extraction from a pair-reduced state which already owns a protected name. -/
noncomputable def finishExtractions {n : ℕ}
    {tokens : List (ReductionToken n)}
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (reduced :
      IsPairReduced (ReductionToken.residualDarts tokens)) :
    MarkedExtractionResult state :=
  finishExtractionsFuel
    (ReductionToken.residualDarts tokens).length
    state protectedNonempty reduced (le_refl _)

/-- Execute the complete marked extraction recursion from an arbitrary pair-reduced valid one-face
word.  The first extraction establishes protected-name ownership; subsequent calls use
`finishExtractions`. -/
noncomputable def normalizePairReducedMarked {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    MarkedExtractionResult
      (MarkedExecutionState.ofWord word valid) := by
  let initialState :=
    MarkedExecutionState.ofWord word valid
  have hword : word ≠ [] := by
    simpa only [Dyck.oneFace_boundary] using
      valid.2.1 (0 : (Dyck.oneFace word).Face)
  have initialReduced :
      IsPairReduced
        (ReductionToken.residualDarts
          (ReductionToken.ofWord word)) := by
    simpa using reduced
  have initialResidualNonempty :
      ReductionToken.residualDarts
          (ReductionToken.ofWord word) ≠ [] := by
    simpa using hword
  let feature :=
    Classical.choice
      (exists_actionablePairReductionFeature_of_usedMultiplicities
        (ReductionToken.residualDarts
          (ReductionToken.ofWord word))
        initialState.hasValidUsedMultiplicities_residualDarts
        initialReduced initialResidualNonempty)
  let marked :=
    MarkedActionablePairReductionFeature.lift feature
  let execution :=
    marked.extract initialState.separated
      initialState.classified initialState.protectedNodup
      initialState.valid
  let extractedState :
      MarkedExecutionState marked.targetTokens :=
    { valid := execution.targetValid
      separated := execution.targetSeparated
      classified := execution.targetClassified
      protectedNodup :=
        execution.targetProtectedNodup }
  let reduction :=
    extractedState.reduceResidualPairs
      marked.protectedNames_targetTokens_ne_nil
  let tail :=
    reduction.targetState.finishExtractions
      reduction.targetProtectedNonempty
      reduction.targetReduced
  exact
    { targetEdgeCount := tail.targetEdgeCount
      targetTokens := tail.targetTokens
      targetState := tail.targetState
      targetProtectedNonempty :=
        tail.targetProtectedNonempty
      targetResidualEmpty := tail.targetResidualEmpty
      equivalent :=
        execution.equivalent.trans
          (reduction.equivalent.trans tail.equivalent) }

end MarkedExecutionState

/-- Exact atom-level endpoint of the marked recursion.  Its name spine is duplicate-free, its
word is surface-valid, and at least one protected atom remains. -/
structure TerminalProtectedWord where
  /-- The `edgeCount` declaration. -/
  edgeCount : ℕ
  /-- The `atoms` declaration. -/
  atoms : List (ProtectedAtom edgeCount)
  atomsNonempty : atoms ≠ []
  namesNodup : (ProtectedAtom.sequenceNames atoms).Nodup
  valid :
    (Dyck.oneFace
      (ProtectedAtom.sequenceWord atoms)).IsSurfaceValid

namespace TerminalProtectedWord

/-- Validity-bundled finite-cyclic presentation displayed by a terminal atom word. -/
def validPresentation (terminal : TerminalProtectedWord) :
    ValidPresentation :=
  ⟨Dyck.oneFace
      (ProtectedAtom.sequenceWord terminal.atoms),
    terminal.valid⟩

/-- Exact canonical normal form selected by a terminal atom word. -/
def normalForm (terminal : TerminalProtectedWord) : NormalForm :=
  ProtectedAtom.normalForm terminal.atoms

/-- A terminal atom word always selects an Eval-admissible canonical presentation. -/
theorem admissible (terminal : TerminalProtectedWord) :
    terminal.normalForm.IsEvalAdmissible :=
  ProtectedAtom.normalForm_isEvalAdmissible_of_ne_nil
    terminal.atoms terminal.atomsNonempty

/-- Retain the terminal atom sequence after adding the fresh boundary-envelope carrier. -/
def retainedAtoms (terminal : TerminalProtectedWord) :
    List (ProtectedAtom (terminal.edgeCount + 1)) :=
  terminal.atoms.map ProtectedAtom.retain

/-- Represent every retained terminal atom as one protected marked token. -/
def retainedTokens (terminal : TerminalProtectedWord) :
    List (ReductionToken (terminal.edgeCount + 1)) :=
  terminal.retainedAtoms.map ReductionToken.ofProtectedAtom

/-- Marked target of the boundary envelope: the fresh opposite carrier pair surrounds all
retained terminal atoms. -/
def envelopedTokens (terminal : TerminalProtectedWord) :
    List (ReductionToken (terminal.edgeCount + 1)) :=
  .residual (.pos (BoundaryEnvelope.carrier terminal.edgeCount)) ::
    terminal.retainedTokens ++
      [.residual
        (.neg (BoundaryEnvelope.carrier terminal.edgeCount))]

@[simp]
theorem expand_retainedTokens
    (terminal : TerminalProtectedWord) :
    ReductionToken.expand terminal.retainedTokens =
      P2.retainWord
        (ProtectedAtom.sequenceWord terminal.atoms) := by
  rw [retainedTokens,
    ReductionToken.expand_map_ofProtectedAtom,
    retainedAtoms,
    ProtectedAtom.sequenceWord_map_retain]

@[simp]
theorem expand_envelopedTokens
    (terminal : TerminalProtectedWord) :
    ReductionToken.expand terminal.envelopedTokens =
      BoundaryEnvelope.targetWord
        (ProtectedAtom.sequenceWord terminal.atoms) := by
  simp [envelopedTokens, BoundaryEnvelope.targetWord]

@[simp]
theorem residualDarts_retainedTokens
    (terminal : TerminalProtectedWord) :
    ReductionToken.residualDarts terminal.retainedTokens = [] := by
  rw [retainedTokens]
  induction terminal.retainedAtoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      simp [ih]

@[simp]
theorem residualDarts_envelopedTokens
    (terminal : TerminalProtectedWord) :
    ReductionToken.residualDarts terminal.envelopedTokens =
      [.pos (BoundaryEnvelope.carrier terminal.edgeCount),
        .neg (BoundaryEnvelope.carrier terminal.edgeCount)] := by
  simp [envelopedTokens]

@[simp]
theorem protectedNames_retainedTokens
    (terminal : TerminalProtectedWord) :
    ReductionToken.protectedNames terminal.retainedTokens =
      (ProtectedAtom.sequenceNames terminal.atoms).map
        Fin.castSucc := by
  rw [retainedTokens,
    ReductionToken.protectedNames_map_ofProtectedAtom,
    retainedAtoms,
    ProtectedAtom.sequenceNames_map_retain]

@[simp]
theorem protectedNames_envelopedTokens
    (terminal : TerminalProtectedWord) :
    ReductionToken.protectedNames terminal.envelopedTokens =
      (ProtectedAtom.sequenceNames terminal.atoms).map
        Fin.castSucc := by
  simp [envelopedTokens]

theorem sequenceNames_ne_nil
    (terminal : TerminalProtectedWord) :
    ProtectedAtom.sequenceNames terminal.atoms ≠ [] := by
  cases hatoms : terminal.atoms with
  | nil =>
      exact (terminal.atomsNonempty hatoms).elim
  | cons atom atoms =>
      rw [ProtectedAtom.sequenceNames_cons]
      cases atom with
      | boundary =>
          simp [ProtectedAtom.names]
      | completed block =>
          cases block <;>
            simp [ProtectedAtom.names, CompletedBlock.names]

theorem protectedNames_envelopedTokens_ne_nil
    (terminal : TerminalProtectedWord) :
    ReductionToken.protectedNames terminal.envelopedTokens ≠ [] := by
  rw [protectedNames_envelopedTokens]
  intro hnil
  rw [List.map_eq_nil_iff] at hnil
  exact terminal.sequenceNames_ne_nil hnil

theorem envelopedSeparated
    (terminal : TerminalProtectedWord) :
    ReductionToken.IsSeparated terminal.envelopedTokens := by
  rw [ReductionToken.IsSeparated, List.disjoint_left]
  intro edge hresidual hprotected
  have hprotectedName :
      edge ∈
        ReductionToken.protectedNames terminal.envelopedTokens :=
    (ReductionToken.mem_protectedNames_iff_mem_protectedEdges
      terminal.envelopedTokens edge).mpr hprotected
  rw [protectedNames_envelopedTokens] at hprotectedName
  rcases List.mem_map.mp hprotectedName with
    ⟨oldEdge, _, hold⟩
  rw [residualDarts_envelopedTokens] at hresidual
  simp only [List.map_cons, List.map_nil, edgeOfDart,
    List.mem_cons, List.not_mem_nil, or_false] at hresidual
  rcases hresidual with hcarrier | hcarrier
  · exact Fin.castSucc_ne_last oldEdge
      (hold.trans hcarrier)
  · exact Fin.castSucc_ne_last oldEdge
      (hold.trans hcarrier)

theorem envelopedClassified
    (terminal : TerminalProtectedWord) :
    ReductionToken.AllClassified terminal.envelopedTokens := by
  unfold envelopedTokens
  apply
    (ReductionToken.allClassified_cons _ _).mpr
  refine ⟨trivial, ?_⟩
  apply ReductionToken.AllClassified.append
  · intro token htoken
    rw [retainedTokens] at htoken
    rcases List.mem_map.mp htoken with
      ⟨atom, _, rfl⟩
    exact ReductionToken.isClassified_ofProtectedAtom atom
  · intro token htoken
    simp only [List.mem_singleton] at htoken
    subst token
    trivial

theorem envelopedProtectedNodup
    (terminal : TerminalProtectedWord) :
    (ReductionToken.protectedNames
      terminal.envelopedTokens).Nodup := by
  rw [protectedNames_envelopedTokens]
  exact terminal.namesNodup.map
    (Fin.castSucc_injective terminal.edgeCount)

/-- Valid marked execution state carried by the fresh boundary envelope. -/
theorem envelopedState
    (terminal : TerminalProtectedWord) :
    MarkedExecutionState terminal.envelopedTokens where
  valid := by
    rw [expand_envelopedTokens]
    exact BoundaryEnvelope.target_isSurfaceValid
      (ProtectedAtom.sequenceWord terminal.atoms)
      terminal.valid
  separated := terminal.envelopedSeparated
  classified := terminal.envelopedClassified
  protectedNodup := terminal.envelopedProtectedNodup

/-- The fresh boundary-envelope carrier as an actionable marked residual pair. -/
def envelopedPair
    (terminal : TerminalProtectedWord) :
    MarkedResidualCancellablePair terminal.envelopedTokens where
  edge := BoundaryEnvelope.carrier terminal.edgeCount
  negativeFirst := false
  betweenTokens := terminal.retainedTokens
  tailTokens := []
  rotated := by
    exact List.IsRotated.refl _
  residual_between := terminal.residualDarts_retainedTokens

/-- Execute the existing protected-interval resolver on the fresh boundary envelope. -/
noncomputable def resolveEnvelope
    (terminal : TerminalProtectedWord) :
    MarkedResidualPairResolution terminal.envelopedPair
      terminal.envelopedState :=
  terminal.envelopedPair.resolve terminal.envelopedState
    terminal.protectedNames_envelopedTokens_ne_nil

theorem resolveEnvelope_residualLength_lt_two
    (terminal : TerminalProtectedWord) :
    (ReductionToken.residualDarts
      terminal.resolveEnvelope.targetTokens).length < 2 := by
  have h :=
    terminal.resolveEnvelope.residualLengthLt
  simpa using h

theorem resolveEnvelope_residualDarts_eq_nil
    (terminal : TerminalProtectedWord) :
    ReductionToken.residualDarts
      terminal.resolveEnvelope.targetTokens = [] := by
  apply List.length_eq_zero_iff.mp
  rw [terminal.resolveEnvelope.residualLengthEqTail]
  rfl

theorem resolveEnvelope_rawBoundaryCount_eq_zero
    (terminal : TerminalProtectedWord) :
    ReductionToken.rawBoundaryCount
      terminal.resolveEnvelope.targetTokens = 0 := by
  rw [terminal.resolveEnvelope.rawBoundaryCountEqTail]
  rfl

/-- Boundary enveloping followed by the existing marked resolver preserves the realization of
the original terminal protected word. -/
theorem normalizationEquivalent_resolveEnvelope
    (terminal : TerminalProtectedWord) :
    NormalizationEquivalent terminal.validPresentation
      ⟨Dyck.oneFace
          (ReductionToken.expand
            terminal.resolveEnvelope.targetTokens),
        terminal.resolveEnvelope.targetState.valid⟩ := by
  have henvelope :=
    BoundaryEnvelope.normalizationEquivalent
      (ProtectedAtom.sequenceWord terminal.atoms)
      (by
        cases hatoms : terminal.atoms with
        | nil =>
            exact (terminal.atomsNonempty hatoms).elim
        | cons atom atoms =>
            rw [ProtectedAtom.sequenceWord_cons]
            cases atom with
            | boundary =>
                simp [ProtectedAtom.word]
            | completed block =>
                cases block <;>
                  simp [ProtectedAtom.word,
                    CompletedBlock.word, boundaryLoopWord])
      terminal.valid
  have htarget :
      (⟨BoundaryEnvelope.target
            (ProtectedAtom.sequenceWord terminal.atoms),
          BoundaryEnvelope.target_isSurfaceValid
            (ProtectedAtom.sequenceWord terminal.atoms)
            terminal.valid⟩ :
        ValidPresentation) =
        ⟨Dyck.oneFace
            (ReductionToken.expand terminal.envelopedTokens),
          terminal.envelopedState.valid⟩ := by
    apply ValidPresentation.ext
    change
      BoundaryEnvelope.target
          (ProtectedAtom.sequenceWord terminal.atoms) =
        Dyck.oneFace
          (ReductionToken.expand terminal.envelopedTokens)
    rw [expand_envelopedTokens]
  exact henvelope.trans
    (htarget ▸ terminal.resolveEnvelope.equivalent)

/-- Finish the fresh-carrier resolution at a certified residual-empty marked endpoint. -/
noncomputable def finishEnvelope
    (terminal : TerminalProtectedWord) :
    MarkedExtractionResult
      terminal.resolveEnvelope.targetState :=
  terminal.resolveEnvelope.targetState.finishExtractions
    terminal.resolveEnvelope.targetProtectedNonempty
    (isPairReduced_of_length_lt_two
      terminal.resolveEnvelope_residualLength_lt_two)

/-- The completely executed boundary-envelope chain preserves the original realization. -/
theorem normalizationEquivalent_finishEnvelope
    (terminal : TerminalProtectedWord) :
    NormalizationEquivalent terminal.validPresentation
      ⟨Dyck.oneFace
          (ReductionToken.expand
            terminal.finishEnvelope.targetTokens),
        terminal.finishEnvelope.targetState.valid⟩ :=
  terminal.normalizationEquivalent_resolveEnvelope.trans
    terminal.finishEnvelope.equivalent

theorem finishEnvelope_residualDarts_eq_nil
    (terminal : TerminalProtectedWord) :
    ReductionToken.residualDarts
      terminal.finishEnvelope.targetTokens = [] :=
  terminal.finishEnvelope.targetResidualEmpty

end TerminalProtectedWord

namespace MarkedExecutionState

/-- Forget the marked-token implementation of a residual-empty state and retain its exact
terminal protected-atom word. -/
noncomputable def toTerminalProtectedWord {n : ℕ}
    {tokens : List (ReductionToken n)}
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (residualEmpty :
      ReductionToken.residualDarts tokens = []) :
    TerminalProtectedWord where
  edgeCount := n
  atoms :=
    ReductionToken.terminalAtoms tokens state.classified
      residualEmpty
  atomsNonempty :=
    ReductionToken.terminalAtoms_ne_nil_of_protectedNames_ne_nil
      tokens state.classified residualEmpty protectedNonempty
  namesNodup := by
    rw [← ReductionToken.protectedNames_map_ofProtectedAtom,
      ← ReductionToken.eq_map_terminalAtoms
        tokens state.classified residualEmpty]
    exact state.protectedNodup
  valid := by
    simpa only [
      ReductionToken.expand_eq_sequenceWord_terminalAtoms
        tokens state.classified residualEmpty] using
      state.valid

theorem expand_eq_toTerminalProtectedWord_sequenceWord {n : ℕ}
    {tokens : List (ReductionToken n)}
    (state : MarkedExecutionState tokens)
    (protectedNonempty :
      ReductionToken.protectedNames tokens ≠ [])
    (residualEmpty :
      ReductionToken.residualDarts tokens = []) :
    ReductionToken.expand tokens =
      ProtectedAtom.sequenceWord
        (state.toTerminalProtectedWord
          protectedNonempty residualEmpty).atoms :=
  ReductionToken.expand_eq_sequenceWord_terminalAtoms
    tokens state.classified residualEmpty

end MarkedExecutionState

/-- Exact block-level endpoint after every raw boundary singleton has been completed. -/
structure TerminalCompletedWord where
  /-- The `edgeCount` declaration. -/
  edgeCount : ℕ
  /-- The `blocks` declaration. -/
  blocks : List (CompletedBlock edgeCount)
  blocksNonempty : blocks ≠ []
  namesNodup : (CompletedBlock.sequenceNames blocks).Nodup
  valid :
    (Dyck.oneFace
      (CompletedBlock.sequenceWord blocks)).IsSurfaceValid

namespace TerminalCompletedWord

/-- Validity-bundled finite-cyclic presentation displayed by a terminal completed-block word. -/
def validPresentation (terminal : TerminalCompletedWord) :
    ValidPresentation :=
  ⟨Dyck.oneFace
      (CompletedBlock.sequenceWord terminal.blocks),
    terminal.valid⟩

/-- Exact canonical normal form selected by the completed block counts. -/
def normalForm (terminal : TerminalCompletedWord) :
    NormalForm :=
  CompletedBlock.normalForm terminal.blocks

theorem admissible (terminal : TerminalCompletedWord) :
    terminal.normalForm.IsEvalAdmissible :=
  CompletedBlock.normalForm_isEvalAdmissible_of_ne_nil
    terminal.blocks terminal.blocksNonempty

end TerminalCompletedWord

namespace TerminalProtectedWord

/-- Atom-level terminal word returned by the fully executed fresh boundary envelope. -/
noncomputable def boundaryNormalizedWord
    (terminal : TerminalProtectedWord) :
    TerminalProtectedWord :=
  terminal.resolveEnvelope.targetState.toTerminalProtectedWord
    terminal.resolveEnvelope.targetProtectedNonempty
    terminal.resolveEnvelope_residualDarts_eq_nil

theorem boundaryNormalizedWord_rawBoundaryCount_eq_zero
    (terminal : TerminalProtectedWord) :
    ProtectedAtom.rawBoundaryCount
      terminal.boundaryNormalizedWord.atoms = 0 := by
  have hraw :=
    terminal.resolveEnvelope_rawBoundaryCount_eq_zero
  rw [ReductionToken.eq_map_terminalAtoms
    terminal.resolveEnvelope.targetTokens
    terminal.resolveEnvelope.targetState.classified
    terminal.resolveEnvelope_residualDarts_eq_nil] at hraw
  simpa [boundaryNormalizedWord,
    MarkedExecutionState.toTerminalProtectedWord] using hraw

/-- The boundary-envelope execution exposes a residual-empty protected atom word equivalent to
the original terminal word. -/
theorem normalizationEquivalent_boundaryNormalizedWord
    (terminal : TerminalProtectedWord) :
    NormalizationEquivalent terminal.validPresentation
      terminal.boundaryNormalizedWord.validPresentation := by
  have htarget :
      (⟨Dyck.oneFace
            (ReductionToken.expand
              terminal.resolveEnvelope.targetTokens),
          terminal.resolveEnvelope.targetState.valid⟩ :
        ValidPresentation) =
        terminal.boundaryNormalizedWord.validPresentation := by
    apply ValidPresentation.ext
    exact congrArg Dyck.oneFace
      (MarkedExecutionState.expand_eq_toTerminalProtectedWord_sequenceWord
        terminal.resolveEnvelope.targetState
        terminal.resolveEnvelope.targetProtectedNonempty
        terminal.resolveEnvelope_residualDarts_eq_nil)
  have hequivalent :
      NormalizationEquivalent
        (⟨Dyck.oneFace
              (ReductionToken.expand
                terminal.resolveEnvelope.targetTokens),
            terminal.resolveEnvelope.targetState.valid⟩ :
          ValidPresentation)
        terminal.boundaryNormalizedWord.validPresentation := by
    rw [← htarget]
    exact NormalizationEquivalent.refl _
  exact terminal.normalizationEquivalent_resolveEnvelope.trans
    hequivalent

/-- Extract the unique completed-block sequence from a raw-free terminal atom word. -/
noncomputable def completedBlocks
    (terminal : TerminalProtectedWord)
    (hraw :
      ProtectedAtom.rawBoundaryCount terminal.atoms = 0) :
    List (CompletedBlock terminal.edgeCount) :=
  Classical.choose
    (ProtectedAtom.exists_eq_map_completed_of_rawBoundaryCount_eq_zero
      terminal.atoms hraw)

theorem atoms_eq_map_completedBlocks
    (terminal : TerminalProtectedWord)
    (hraw :
      ProtectedAtom.rawBoundaryCount terminal.atoms = 0) :
    terminal.atoms =
      (terminal.completedBlocks hraw).map .completed :=
  Classical.choose_spec
    (ProtectedAtom.exists_eq_map_completed_of_rawBoundaryCount_eq_zero
      terminal.atoms hraw)

theorem completedBlocks_ne_nil
    (terminal : TerminalProtectedWord)
    (hraw :
      ProtectedAtom.rawBoundaryCount terminal.atoms = 0) :
    terminal.completedBlocks hraw ≠ [] := by
  intro hnil
  apply terminal.atomsNonempty
  rw [terminal.atoms_eq_map_completedBlocks hraw, hnil]
  rfl

/-- Completed-block endpoint selected by the fully executed boundary normalization. -/
noncomputable def boundaryCompletedWord
    (terminal : TerminalProtectedWord) :
    TerminalCompletedWord where
  edgeCount := terminal.boundaryNormalizedWord.edgeCount
  blocks :=
    terminal.boundaryNormalizedWord.completedBlocks
      terminal.boundaryNormalizedWord_rawBoundaryCount_eq_zero
  blocksNonempty :=
    terminal.boundaryNormalizedWord.completedBlocks_ne_nil
      terminal.boundaryNormalizedWord_rawBoundaryCount_eq_zero
  namesNodup := by
    rw [← ProtectedAtom.sequenceNames_map_completed,
      ← terminal.boundaryNormalizedWord.atoms_eq_map_completedBlocks
        terminal.boundaryNormalizedWord_rawBoundaryCount_eq_zero]
    exact terminal.boundaryNormalizedWord.namesNodup
  valid := by
    rw [← ProtectedAtom.sequenceWord_map_completed,
      ← terminal.boundaryNormalizedWord.atoms_eq_map_completedBlocks
        terminal.boundaryNormalizedWord_rawBoundaryCount_eq_zero]
    exact terminal.boundaryNormalizedWord.valid

/-- Boundary normalization lands exactly in the completed-block terminal interface. -/
theorem normalizationEquivalent_boundaryCompletedWord
    (terminal : TerminalProtectedWord) :
    NormalizationEquivalent terminal.validPresentation
      terminal.boundaryCompletedWord.validPresentation := by
  have htarget :
      terminal.boundaryNormalizedWord.validPresentation =
        terminal.boundaryCompletedWord.validPresentation := by
    apply ValidPresentation.ext
    change
      Dyck.oneFace
          (ProtectedAtom.sequenceWord
            terminal.boundaryNormalizedWord.atoms) =
        Dyck.oneFace
          (CompletedBlock.sequenceWord
            terminal.boundaryCompletedWord.blocks)
    rw [terminal.boundaryNormalizedWord.atoms_eq_map_completedBlocks
      terminal.boundaryNormalizedWord_rawBoundaryCount_eq_zero]
    exact congrArg Dyck.oneFace
      (ProtectedAtom.sequenceWord_map_completed _)
  have hequivalent :
      NormalizationEquivalent
        terminal.boundaryNormalizedWord.validPresentation
        terminal.boundaryCompletedWord.validPresentation := by
    rw [← htarget]
    exact NormalizationEquivalent.refl _
  exact
    terminal.normalizationEquivalent_boundaryNormalizedWord.trans
      hequivalent

/-- Exact normal form selected after constructive raw-boundary completion. -/
noncomputable def completedNormalForm
    (terminal : TerminalProtectedWord) :
    NormalForm :=
  terminal.boundaryCompletedWord.normalForm

theorem completedAdmissible
    (terminal : TerminalProtectedWord) :
    terminal.completedNormalForm.IsEvalAdmissible :=
  terminal.boundaryCompletedWord.admissible

end TerminalProtectedWord

/-- The isolated terminal obligation after the terminating marked recursion: normalize a valid,
classified marked word whose residual contribution is empty. -/
structure TerminalMarkedNormalizer where
  /-- The `normalize` declaration. -/
  normalize :
    {n : ℕ} →
      {tokens : List (ReductionToken n)} →
      (state : MarkedExecutionState tokens) →
      ReductionToken.protectedNames tokens ≠ [] →
      ReductionToken.residualDarts tokens = [] →
      NormalizationResult
        ⟨Dyck.oneFace (ReductionToken.expand tokens),
          state.valid⟩

/-- Narrow completed-block obligation: order and orient a valid, nonempty, duplicate-free block
sequence and perform the nonorientable handle conversion. -/
structure TerminalCompletedNormalizer where
  equivalent :
    (terminal : TerminalCompletedWord) →
      NormalizationEquivalent terminal.validPresentation
        (canonicalValidPresentation terminal.normalForm
          terminal.admissible)

/-- Narrow terminal obligation at the proof's stable seam: normalize a duplicate-free nonempty
sequence of protected atoms to the exact canonical presentation selected after boundary
completion. -/
structure TerminalProtectedNormalizer where
  equivalent :
    (terminal : TerminalProtectedWord) →
      NormalizationEquivalent terminal.validPresentation
        (canonicalValidPresentation terminal.completedNormalForm
          terminal.completedAdmissible)

namespace TerminalCompletedNormalizer

/-- A completed-block normalizer discharges the protected-word seam after constructive boundary
completion. -/
theorem toTerminalProtectedNormalizer
    (normalizer : TerminalCompletedNormalizer) :
    TerminalProtectedNormalizer where
  equivalent terminal :=
    terminal.normalizationEquivalent_boundaryCompletedWord.trans
      (normalizer.equivalent terminal.boundaryCompletedWord)

end TerminalCompletedNormalizer

namespace TerminalProtectedNormalizer

/-- Package a protected-word terminal equivalence as the standard exact normalization result. -/
noncomputable def normalize
    (normalizer : TerminalProtectedNormalizer)
    (terminal : TerminalProtectedWord) :
    NormalizationResult terminal.validPresentation where
  normalForm := terminal.completedNormalForm
  admissible := terminal.completedAdmissible
  equivalent := normalizer.equivalent terminal

/-- A protected-word normalizer discharges the token-level terminal interface used by the marked
extraction recursion. -/
noncomputable def toTerminalMarkedNormalizer
    (normalizer : TerminalProtectedNormalizer) :
    TerminalMarkedNormalizer where
  normalize state protectedNonempty residualEmpty := by
    let terminal :=
      state.toTerminalProtectedWord
        protectedNonempty residualEmpty
    have hsource :
        (⟨Dyck.oneFace
              (ReductionToken.expand _),
            state.valid⟩ :
          ValidPresentation) =
          terminal.validPresentation := by
      apply ValidPresentation.ext
      exact congrArg Dyck.oneFace
        (state.expand_eq_toTerminalProtectedWord_sequenceWord
          protectedNonempty residualEmpty)
    rw [hsource]
    exact normalizer.normalize terminal

end TerminalProtectedNormalizer

/-- A terminal block normalizer supplies the remaining `PairReducedNormalizer` field after the
now-complete marked extraction recursion. -/
noncomputable def pairReducedNormalizerOfTerminal
    (terminal : TerminalMarkedNormalizer) :
    PairReducedNormalizer where
  normalize word valid reduced := by
    let extraction :=
      MarkedExecutionState.normalizePairReducedMarked
        word valid reduced
    have hExtraction :
        NormalizationEquivalent
          ⟨Dyck.oneFace word, valid⟩
          ⟨Dyck.oneFace
              (ReductionToken.expand extraction.targetTokens),
            extraction.targetState.valid⟩ := by
      simpa using extraction.equivalent
    exact
      (terminal.normalize extraction.targetState
          extraction.targetProtectedNonempty
          extraction.targetResidualEmpty).ofEquivalent
        hExtraction

/-- The universal connected normalization theorem is reduced to the explicit terminal block
normalizer, with face merging, initial cancellation, marked extraction, and canonical-result
composition already discharged. -/
noncomputable def normalizeConnectedOfTerminal
    (terminal : TerminalMarkedNormalizer)
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    NormalizationResult P :=
  normalizeConnected
    (pairReducedNormalizerOfTerminal terminal)
    P connectedP

end Pairing

end WordReduction

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
