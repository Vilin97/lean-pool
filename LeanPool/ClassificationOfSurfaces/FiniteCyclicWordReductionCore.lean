/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCancellation
import LeanPool.ClassificationOfSurfaces.FiniteCyclicReduction
import LeanPool.ClassificationOfSurfaces.FiniteCyclicNormalizationResult

/-!
# Recursive reduction of finite cyclic one-face words

The face-merging recursion deliberately retains each deleted separator as a cyclically adjacent
inverse pair.  This file supplies the next normalization phase: repeatedly cancel every such pair
while preserving a validity-bundled normalization chain.  If the final pair is the whole word,
the result is the agreed ordinary-valid two-monogon sphere presentation.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

/-- The unique face of a presentation whose stored face list has length one. -/
def onlyFace (P : FiniteCyclicPresentation) (hfaces : P.faces.length = 1) :
    P.Face :=
  ⟨0, by omega⟩

/-- Rewrite an arbitrary one-face presentation using its unique stored boundary word. -/
@[reducible]
def explicitOneFace
    (P : FiniteCyclicPresentation) (hfaces : P.faces.length = 1) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (P.boundary (onlyFace P hfaces))

/-- Every presentation with one stored face is signed-isomorphic to its explicit one-word
spelling. -/
def explicitOneFaceSignedIso
    (P : FiniteCyclicPresentation) (hfaces : P.faces.length = 1) :
    SignedPresentationIso P (explicitOneFace P hfaces) where
  edgeRelabeling := EdgeRelabeling.refl _
  faceEquiv := by
    change Fin P.faces.length ≃ Fin 1
    exact finCongr hfaces
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_refl, Dyck.oneFace_boundary]
    have hf : f = onlyFace P hfaces := by
      apply Fin.ext
      have hflt := f.isLt
      change f.val < P.faces.length at hflt
      change f.val = 0
      omega
    rw [hf]

/-- Relabel a finished `Fin`-indexed one-face word directly to the existing typed one-face
adapter.  This is the final bridge used by canonical normalization; it does not introduce a
second spelling of any Lean-Eval representative. -/
noncomputable def oneFaceSignedIsoToOfOneFaceWord {n : ℕ}
    {Edge : Type} [Fintype Edge]
    (sourceWord : List (SignedDart (Fin n)))
    (typedWord : List (SignedDart Edge))
    (edgeEquiv : Fin n ≃ Edge)
    (rotated :
      (sourceWord.map (SignedDart.mapEquiv edgeEquiv)).IsRotated
        typedWord) :
    SignedPresentationIso
      (Dyck.oneFace sourceWord)
      (ofOneFaceWord typedWord) where
  edgeRelabeling :=
    EdgeRelabeling.ofEquiv
      (edgeEquiv.trans (Fintype.equivFin Edge))
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, ofOneFaceWord_boundary,
      EdgeRelabeling.map_mapDart_ofEquiv,
      map_mapEquiv_trans]
    exact rotated.map
      (SignedDart.mapEquiv (Fintype.equivFin Edge))

/-- Signed version of the finished one-face adapter.  In addition to renaming edge names, this
allows each finished block edge to be reversed independently before landing at the single
project-owned canonical word. -/
noncomputable def oneFaceSignedIsoToOfOneFaceWordRelabeling {n : ℕ}
    {Edge : Type} [Fintype Edge]
    (sourceWord : List (SignedDart (Fin n)))
    (typedWord : List (SignedDart Edge))
    (edgeRelabeling : EdgeRelabeling (Fin n) Edge)
    (rotated :
      (sourceWord.map edgeRelabeling.mapDart).IsRotated
        typedWord) :
    SignedPresentationIso
      (Dyck.oneFace sourceWord)
      (ofOneFaceWord typedWord) where
  edgeRelabeling :=
    edgeRelabeling.trans
      (EdgeRelabeling.ofEquiv (Fintype.equivFin Edge))
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, ofOneFaceWord_boundary,
      EdgeRelabeling.map_mapDart_trans,
      EdgeRelabeling.map_mapDart_ofEquiv]
    exact rotated.map
      (SignedDart.mapEquiv (Fintype.equivFin Edge))

/-- A finished orientable word, up to its explicit edge relabeling and cyclic rotation, gives a
normalization result at the exact existing orientable canonical presentation. -/
noncomputable def orientableNormalizationResultOfRotated
    {k p n : ℕ}
    (sourceWord : List (SignedDart (Fin k)))
    (edgeEquiv : Fin k ≃ NormalForm.OrientableEdge p n)
    (rotated :
      (sourceWord.map (SignedDart.mapEquiv edgeEquiv)).IsRotated
        (NormalForm.orientableBoundaryWord p n))
    (valid : (Dyck.oneFace sourceWord).IsSurfaceValid)
    (admissible : (NormalForm.orientable p n).IsEvalAdmissible) :
    NormalizationResult ⟨Dyck.oneFace sourceWord, valid⟩ :=
  (NormalizationResult.canonical
      (NormalForm.orientable p n) admissible).ofSignedIso
    (oneFaceSignedIsoToOfOneFaceWord
      sourceWord (NormalForm.orientableBoundaryWord p n)
      edgeEquiv rotated)

/-- A finished nonorientable word, up to its explicit edge relabeling and cyclic rotation, gives
a normalization result at the exact existing nonorientable canonical presentation. -/
noncomputable def nonOrientableNormalizationResultOfRotated
    {k p n : ℕ}
    (sourceWord : List (SignedDart (Fin k)))
    (edgeEquiv : Fin k ≃ NormalForm.NonOrientableEdge p n)
    (rotated :
      (sourceWord.map (SignedDart.mapEquiv edgeEquiv)).IsRotated
        (NormalForm.nonOrientableBoundaryWord p n))
    (valid : (Dyck.oneFace sourceWord).IsSurfaceValid)
    (admissible :
      (NormalForm.nonOrientable p n).IsEvalAdmissible) :
    NormalizationResult ⟨Dyck.oneFace sourceWord, valid⟩ :=
  (NormalizationResult.canonical
      (NormalForm.nonOrientable p n) admissible).ofSignedIso
    (oneFaceSignedIsoToOfOneFaceWord
      sourceWord (NormalForm.nonOrientableBoundaryWord p n)
      edgeEquiv rotated)

/-- Signed finished orientable word adapter, permitting independent orientation normalization of
every handle and boundary-loop edge. -/
noncomputable def orientableNormalizationResultOfSignedRotated
    {k p n : ℕ}
    (sourceWord : List (SignedDart (Fin k)))
    (edgeRelabeling :
      EdgeRelabeling (Fin k)
        (NormalForm.OrientableEdge p n))
    (rotated :
      (sourceWord.map edgeRelabeling.mapDart).IsRotated
        (NormalForm.orientableBoundaryWord p n))
    (valid : (Dyck.oneFace sourceWord).IsSurfaceValid)
    (admissible : (NormalForm.orientable p n).IsEvalAdmissible) :
    NormalizationResult ⟨Dyck.oneFace sourceWord, valid⟩ :=
  (NormalizationResult.canonical
      (NormalForm.orientable p n) admissible).ofSignedIso
    (oneFaceSignedIsoToOfOneFaceWordRelabeling
      sourceWord (NormalForm.orientableBoundaryWord p n)
      edgeRelabeling rotated)

/-- Signed finished nonorientable word adapter, permitting independent orientation normalization
of every crosscap and boundary-loop edge. -/
noncomputable def nonOrientableNormalizationResultOfSignedRotated
    {k p n : ℕ}
    (sourceWord : List (SignedDart (Fin k)))
    (edgeRelabeling :
      EdgeRelabeling (Fin k)
        (NormalForm.NonOrientableEdge p n))
    (rotated :
      (sourceWord.map edgeRelabeling.mapDart).IsRotated
        (NormalForm.nonOrientableBoundaryWord p n))
    (valid : (Dyck.oneFace sourceWord).IsSurfaceValid)
    (admissible :
      (NormalForm.nonOrientable p n).IsEvalAdmissible) :
    NormalizationResult ⟨Dyck.oneFace sourceWord, valid⟩ :=
  (NormalizationResult.canonical
      (NormalForm.nonOrientable p n) admissible).ofSignedIso
    (oneFaceSignedIsoToOfOneFaceWordRelabeling
      sourceWord (NormalForm.nonOrientableBoundaryWord p n)
      edgeRelabeling rotated)

/-- The two possible signed spellings of an adjacent inverse pair. -/
def inversePair {Edge : Type} (a : Edge) : Bool → List (SignedDart Edge)
  | false => [.pos a, .neg a]
  | true => [.neg a, .pos a]

/-- Data exposing a cyclically adjacent inverse pair in a one-face word. -/
structure CancellablePair {n : ℕ}
    (word : List (SignedDart (Fin n))) where
  /-- The `edge` declaration. -/
  edge : Fin n
  /-- The `tail` declaration. -/
  tail : List (SignedDart (Fin n))
  /-- The `negativeFirst` declaration. -/
  negativeFirst : Bool
  rotated : word.IsRotated (inversePair edge negativeFirst ++ tail)

/-- A one-face word has no cyclically adjacent inverse pair. -/
def IsPairReduced {n : ℕ}
    (word : List (SignedDart (Fin n))) : Prop :=
  IsEmpty (CancellablePair word)

/-- A word with fewer than two darts cannot contain a cyclically adjacent inverse pair. -/
theorem isPairReduced_of_length_lt_two {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (hshort : word.length < 2) :
    IsPairReduced word := by
  constructor
  intro pair
  have hlength := pair.rotated.perm.length_eq
  have hpairLength :
      (inversePair pair.edge pair.negativeFirst).length = 2 := by
    cases pair.negativeFirst <;> rfl
  rw [List.length_append, hpairLength] at hlength
  omega

/-- Validity forces the displayed inverse pair's edge to be absent from its remaining tail. -/
theorem CancellablePair.edge_not_mem_tail {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    pair.edge ∉ pair.tail.map edgeOfDart := by
  intro htail
  have hpositive :
      0 < (pair.tail.map edgeOfDart).count pair.edge :=
    List.count_pos_iff.mpr htail
  have hcount :=
    (pair.rotated.map edgeOfDart).perm.count_eq pair.edge
  have hmultiplicity := valid.2.2.2 pair.edge
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  have hcount' :
      (word.map edgeOfDart).count pair.edge =
        2 + (pair.tail.map edgeOfDart).count pair.edge := by
    rw [hcount]
    cases pair.negativeFirst <;>
      simp [inversePair, edgeOfDart] <;>
      omega
  omega

/-- If deleting a displayed pair leaves the empty word, there were no other edge names. -/
theorem predecessor_eq_zero_of_lowerTail_eq_nil {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : Cancellation.lowerTail a X = [])
    (valid : (Cancellation.namedSource a X).IsSurfaceValid) :
    n = 0 := by
  have hrenamed :
      Cancellation.renamedTail a X = [] := by
    rw [← Cancellation.retainWord_lowerTail a X ha, hlower]
    rfl
  have hX : X = [] := by
    simpa [Cancellation.renamedTail] using hrenamed
  by_contra hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let e : Fin n := ⟨0, hnpos⟩
  let b : Fin (n + 1) :=
    (Cancellation.moveToLast a).symm e.castSucc
  have hba : b ≠ a := by
    intro h
    have hmapped := congrArg (Cancellation.moveToLast a) h
    have hbmap :
        Cancellation.moveToLast a b = e.castSucc := by
      exact (Cancellation.moveToLast a).apply_symm_apply e.castSucc
    rw [hbmap] at hmapped
    rw [show Cancellation.moveToLast a a = Fin.last n by
      simp [Cancellation.moveToLast]]
      at hmapped
    exact Fin.castSucc_ne_last e hmapped
  have hmultiplicity := valid.2.2.2 b
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  simp [hX, edgeOfDart, hba.symm] at hmultiplicity

/-- A reduced non-spherical endpoint reached after inverse-pair cancellation. -/
structure ReducedWordResult (P : ValidPresentation) where
  /-- The `edgeCount` declaration. -/
  edgeCount : ℕ
  /-- The `word` declaration. -/
  word : List (SignedDart (Fin edgeCount))
  valid : (Dyck.oneFace word).IsSurfaceValid
  reduced : IsPairReduced word
  equivalent :
    NormalizationEquivalent P ⟨Dyck.oneFace word, valid⟩

/-- Cancellation either reaches the canonical sphere presentation or a pair-reduced one-face
word. -/
inductive CancellationResult (P : ValidPresentation)
  | sphere
      (equivalent :
        NormalizationEquivalent P
          ⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩)
  | reduced (result : ReducedWordResult P)

namespace CancellationResult

/-- Transport a cancellation result backward through a normalization equivalence. -/
noncomputable def ofEquivalent {P Q : ValidPresentation}
    (hPQ : NormalizationEquivalent P Q) :
    CancellationResult Q → CancellationResult P
  | .sphere hQS => .sphere (hPQ.trans hQS)
  | .reduced result =>
      .reduced
        { edgeCount := result.edgeCount
          word := result.word
          valid := result.valid
          reduced := result.reduced
          equivalent := hPQ.trans result.equivalent }

/-- Finish a cancellation result once pair-reduced one-face words have a canonical normalizer. -/
noncomputable def finish {P : ValidPresentation}
    (normalizeReduced :
      (result : ReducedWordResult P) →
        NormalizationResult
          ⟨Dyck.oneFace result.word, result.valid⟩) :
    CancellationResult P → NormalizationResult P
  | .sphere hSphere => by
      have hnode :
          (⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ :
            ValidPresentation) =
            canonicalValidPresentation NormalForm.sphere trivial := by
        apply ValidPresentation.ext
        rfl
      rw [hnode] at hSphere
      exact
        { normalForm := .sphere
          admissible := trivial
          equivalent := hSphere }
  | .reduced result =>
      (normalizeReduced result).ofEquivalent result.equivalent

end CancellationResult

/-- If cancelling a displayed inverse pair leaves no tail, the source normalizes to the sphere. -/
private noncomputable def cancellationResult_sphere_of_lowerTail_eq_nil {n : ℕ}
    {word : List (SignedDart (Fin (n + 1)))} (pair : CancellablePair word)
    (ha : pair.edge ∉ pair.tail.map edgeOfDart)
    (hlower : Cancellation.lowerTail pair.edge pair.tail = [])
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    CancellationResult ⟨Dyck.oneFace word, valid⟩ := by
  let a := pair.edge
  let X := pair.tail
  cases horientation : pair.negativeFirst
  · have hrotated : word.IsRotated ([.pos a, .neg a] ++ X) := by
      simpa [a, X, inversePair, horientation] using pair.rotated
    let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
    let validNamed : (Cancellation.namedSource a X).IsSurfaceValid :=
      rotation.isSurfaceValid valid
    have hnzero := predecessor_eq_zero_of_lowerTail_eq_nil a X ha hlower validNamed
    subst n
    let renameIso := Cancellation.namedSourceSignedIso a X ha
    let validBase : (Cancellation.source (Cancellation.lowerTail a X)).IsSurfaceValid :=
      renameIso.isSurfaceValid validNamed
    have hRotate : NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩ ⟨Cancellation.namedSource a X, validNamed⟩ :=
      NormalizationEquivalent.ofSignedIso rotation
    have hRename : NormalizationEquivalent
        ⟨Cancellation.namedSource a X, validNamed⟩
        ⟨Cancellation.source (Cancellation.lowerTail a X), validBase⟩ :=
      NormalizationEquivalent.ofSignedIso renameIso
    have hToBase : NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Cancellation.source (Cancellation.lowerTail a X), validBase⟩ :=
      hRotate.trans hRename
    have hbase : Cancellation.source (Cancellation.lowerTail a X) =
        Cancellation.source ([] : List (SignedDart (Fin 0))) :=
      congrArg Cancellation.source hlower
    let validEmpty :
        (Cancellation.source ([] : List (SignedDart (Fin 0)))).IsSurfaceValid :=
      hbase ▸ validBase
    have hnode :
        (⟨Cancellation.source (Cancellation.lowerTail a X), validBase⟩ :
            ValidPresentation) =
          ⟨Cancellation.source ([] : List (SignedDart (Fin 0))), validEmpty⟩ :=
      ValidPresentation.ext hbase
    rw [hnode] at hToBase
    exact .sphere
      (hToBase.trans (Cancellation.sphereNormalizationEquivalent validEmpty))
  · have hrotated : word.IsRotated ([.neg a, .pos a] ++ X) := by
      simpa [a, X, inversePair, horientation] using pair.rotated
    let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
    let validNegative : (Cancellation.negativeNamedSource a X).IsSurfaceValid :=
      rotation.isSurfaceValid valid
    let signIso := Cancellation.negativeNamedSourceSignedIso a X ha
    let validNamed : (Cancellation.namedSource a X).IsSurfaceValid :=
      signIso.isSurfaceValid validNegative
    have hnzero := predecessor_eq_zero_of_lowerTail_eq_nil a X ha hlower validNamed
    subst n
    let renameIso := Cancellation.namedSourceSignedIso a X ha
    let validBase : (Cancellation.source (Cancellation.lowerTail a X)).IsSurfaceValid :=
      renameIso.isSurfaceValid validNamed
    have hRotate : NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Cancellation.negativeNamedSource a X, validNegative⟩ :=
      NormalizationEquivalent.ofSignedIso rotation
    have hSign : NormalizationEquivalent
        ⟨Cancellation.negativeNamedSource a X, validNegative⟩
        ⟨Cancellation.namedSource a X, validNamed⟩ :=
      NormalizationEquivalent.ofSignedIso signIso
    have hRename : NormalizationEquivalent
        ⟨Cancellation.namedSource a X, validNamed⟩
        ⟨Cancellation.source (Cancellation.lowerTail a X), validBase⟩ :=
      NormalizationEquivalent.ofSignedIso renameIso
    have hToBase : NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Cancellation.source (Cancellation.lowerTail a X), validBase⟩ :=
      hRotate.trans (hSign.trans hRename)
    have hbase : Cancellation.source (Cancellation.lowerTail a X) =
        Cancellation.source ([] : List (SignedDart (Fin 0))) :=
      congrArg Cancellation.source hlower
    let validEmpty :
        (Cancellation.source ([] : List (SignedDart (Fin 0)))).IsSurfaceValid :=
      hbase ▸ validBase
    have hnode :
        (⟨Cancellation.source (Cancellation.lowerTail a X), validBase⟩ :
            ValidPresentation) =
          ⟨Cancellation.source ([] : List (SignedDart (Fin 0))), validEmpty⟩ :=
      ValidPresentation.ext hbase
    rw [hnode] at hToBase
    exact .sphere
      (hToBase.trans (Cancellation.sphereNormalizationEquivalent validEmpty))

/-- A displayed inverse pair with nonempty lower tail gives one certified cancellation step. -/
private theorem exists_cancellationStep_of_lowerTail_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin (n + 1)))} (pair : CancellablePair word)
    (ha : pair.edge ∉ pair.tail.map edgeOfDart)
    (hlower : Cancellation.lowerTail pair.edge pair.tail ≠ [])
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ∃ validLower :
        (Cancellation.target
          (Cancellation.lowerTail pair.edge pair.tail)).IsSurfaceValid,
      NormalizationEquivalent ⟨Dyck.oneFace word, valid⟩
        ⟨Cancellation.target (Cancellation.lowerTail pair.edge pair.tail), validLower⟩ := by
  let a := pair.edge
  let X := pair.tail
  let lower := Cancellation.lowerTail a X
  cases horientation : pair.negativeFirst
  · have hrotated : word.IsRotated ([.pos a, .neg a] ++ X) := by
      simpa [a, X, inversePair, horientation] using pair.rotated
    let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
    let validNamed : (Cancellation.namedSource a X).IsSurfaceValid :=
      rotation.isSurfaceValid valid
    let renameIso := Cancellation.namedSourceSignedIso a X ha
    let validBase : (Cancellation.source lower).IsSurfaceValid :=
      renameIso.isSurfaceValid validNamed
    let validLower : (Cancellation.target lower).IsSurfaceValid :=
      Cancellation.target_isSurfaceValid lower hlower validBase
    have hRotate : NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩ ⟨Cancellation.namedSource a X, validNamed⟩ :=
      NormalizationEquivalent.ofSignedIso rotation
    have hRename : NormalizationEquivalent
        ⟨Cancellation.namedSource a X, validNamed⟩
        ⟨Cancellation.source lower, validBase⟩ :=
      NormalizationEquivalent.ofSignedIso renameIso
    refine ⟨validLower, ?_⟩
    exact hRotate.trans
      (hRename.trans
        (Cancellation.normalizationEquivalent lower hlower validBase))
  · have hrotated : word.IsRotated ([.neg a, .pos a] ++ X) := by
      simpa [a, X, inversePair, horientation] using pair.rotated
    let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
    let validNegative : (Cancellation.negativeNamedSource a X).IsSurfaceValid :=
      rotation.isSurfaceValid valid
    let signIso := Cancellation.negativeNamedSourceSignedIso a X ha
    let validNamed : (Cancellation.namedSource a X).IsSurfaceValid :=
      signIso.isSurfaceValid validNegative
    let renameIso := Cancellation.namedSourceSignedIso a X ha
    let validBase : (Cancellation.source lower).IsSurfaceValid :=
      renameIso.isSurfaceValid validNamed
    let validLower : (Cancellation.target lower).IsSurfaceValid :=
      Cancellation.target_isSurfaceValid lower hlower validBase
    have hRotate : NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Cancellation.negativeNamedSource a X, validNegative⟩ :=
      NormalizationEquivalent.ofSignedIso rotation
    have hSign : NormalizationEquivalent
        ⟨Cancellation.negativeNamedSource a X, validNegative⟩
        ⟨Cancellation.namedSource a X, validNamed⟩ :=
      NormalizationEquivalent.ofSignedIso signIso
    have hRename : NormalizationEquivalent
        ⟨Cancellation.namedSource a X, validNamed⟩
        ⟨Cancellation.source lower, validBase⟩ :=
      NormalizationEquivalent.ofSignedIso renameIso
    refine ⟨validLower, ?_⟩
    exact hRotate.trans
      (hSign.trans
        (hRename.trans
          (Cancellation.normalizationEquivalent lower hlower validBase)))

/-- Fuel-bounded implementation of repeated inverse-pair cancellation. -/
noncomputable def cancelInversePairsFuel (fuel : ℕ) {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    word.length ≤ fuel →
      CancellationResult ⟨Dyck.oneFace word, valid⟩ := by
  classical
  intro hbound
  by_cases hpairs : Nonempty (CancellablePair word)
  · let pair := Classical.choice hpairs
    cases n with
    | zero =>
        exact Fin.elim0 pair.edge
    | succ n =>
        let a : Fin (n + 1) := pair.edge
        let X : List (SignedDart (Fin (n + 1))) := pair.tail
        have ha : a ∉ X.map edgeOfDart :=
          pair.edge_not_mem_tail valid
        let lower := Cancellation.lowerTail a X
        have hlowerLength : lower.length = X.length := by
          have hlength :=
            congrArg List.length
              (Cancellation.retainWord_lowerTail a X ha)
          simpa [lower, P2.retainWord,
            Cancellation.renamedTail] using hlength
        have hwordLength :
            word.length = 2 + X.length := by
          have hlength := pair.rotated.perm.length_eq
          cases horientation : pair.negativeFirst
          · have hlength' :
                word.length = X.length + 1 + 1 := by
              simpa [a, X, inversePair, horientation] using hlength
            omega
          · have hlength' :
                word.length = X.length + 1 + 1 := by
              simpa [a, X, inversePair, horientation] using hlength
            omega
        have hlowerShorter : lower.length < word.length := by
          omega
        have hfuelPositive : 0 < fuel := by
          omega
        have hlowerBound : lower.length ≤ fuel - 1 := by
          omega
        by_cases hlower : lower = []
        · exact cancellationResult_sphere_of_lowerTail_eq_nil pair ha hlower valid
        · let stepWitness :=
            exists_cancellationStep_of_lowerTail_ne_nil pair ha hlower valid
          let validLower := Classical.choose stepWitness
          have hstep := Classical.choose_spec stepWitness
          exact (cancelInversePairsFuel (fuel - 1) lower validLower hlowerBound).ofEquivalent hstep
  · exact .reduced
      { edgeCount := n
        word := word
        valid := valid
        reduced := ⟨fun pair ↦ hpairs ⟨pair⟩⟩
        equivalent := NormalizationEquivalent.refl _ }
termination_by fuel
decreasing_by
  all_goals
    apply Nat.sub_lt
    · exact hfuelPositive
    · omega

/-- Repeatedly cancel cyclically adjacent inverse pairs in an ordinary-valid one-face word. -/
noncomputable def cancelInversePairs {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    CancellationResult ⟨Dyck.oneFace word, valid⟩ :=
  cancelInversePairsFuel word.length word valid (le_refl _)

/-- Merge a connected valid presentation to one face, rewrite that face explicitly as a cyclic
word, and cancel every adjacent inverse pair. -/
noncomputable def reduceAndCancel
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    CancellationResult P := by
  let oneFace := Reduction.reduceToOneFace P connectedP
  let word :=
    oneFace.target.presentation.boundary
      (onlyFace oneFace.target.presentation oneFace.faces_length)
  let iso :=
    explicitOneFaceSignedIso
      oneFace.target.presentation oneFace.faces_length
  let validWord : (Dyck.oneFace word).IsSurfaceValid :=
    iso.isSurfaceValid oneFace.target.valid
  have hToWord :
      NormalizationEquivalent P
        ⟨Dyck.oneFace word, validWord⟩ :=
    oneFace.equivalent.trans
      (NormalizationEquivalent.ofSignedIso iso)
  exact (cancelInversePairs word validWord).ofEquivalent hToWord

/-- The remaining proof obligation after face merging and inverse-pair cancellation: normalize
an arbitrary pair-reduced valid one-face word. -/
structure PairReducedNormalizer where
  /-- The `normalize` declaration. -/
  normalize :
    {n : ℕ} →
      (word : List (SignedDart (Fin n))) →
      (valid : (Dyck.oneFace word).IsSurfaceValid) →
      IsPairReduced word →
      NormalizationResult ⟨Dyck.oneFace word, valid⟩

/-- A normalizer for pair-reduced words completes the faithful finite-cyclic Gallier--Xu
normalization theorem for every connected valid presentation. -/
noncomputable def normalizeConnected
    (normalizer : PairReducedNormalizer)
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    NormalizationResult P :=
  (reduceAndCancel P connectedP).finish fun result ↦
    normalizer.normalize
      result.word result.valid result.reduced

/-! ### Certified occurrence decompositions for the remaining pairing reduction -/

namespace Pairing

/-- A signed dart with its orientation represented by a Boolean. -/
def dart {α : Type*} (a : α) : Bool → SignedDart α
  | false => .pos a
  | true => .neg a

/-- Boolean orientation of a signed dart. -/
def dartNegative {α : Type*} : SignedDart α → Bool
  | .pos _ => false
  | .neg _ => true

/-- An edge equivalence equipped with an explicit source-orientation normalization function. -/
def signedRelabeling {α β : Type*}
    (edgeEquiv : α ≃ β) (reverse : α → Bool) :
    EdgeRelabeling α β where
  edgeEquiv := edgeEquiv
  reverse := reverse

@[simp]
theorem signedRelabeling_edgeEquiv {α β : Type*}
    (edgeEquiv : α ≃ β) (reverse : α → Bool) :
    (signedRelabeling edgeEquiv reverse).edgeEquiv =
      edgeEquiv :=
  rfl

@[simp]
theorem signedRelabeling_reverse {α β : Type*}
    (edgeEquiv : α ≃ β) (reverse : α → Bool)
    (a : α) :
    (signedRelabeling edgeEquiv reverse).reverse a =
      reverse a :=
  rfl

@[simp]
theorem edgeOfDart_dart {α : Type*} (a : α) (negative : Bool) :
    edgeOfDart (dart a negative) = a := by
  cases negative <;> rfl

@[simp]
theorem edgeOfDart_pos {α : Type*} (a : α) :
    edgeOfDart (.pos a) = a := rfl

@[simp]
theorem edgeOfDart_neg {α : Type*} (a : α) :
    edgeOfDart (.neg a) = a := rfl

@[simp]
theorem dart_edgeOfDart_dartNegative {α : Type*}
    (d : SignedDart α) :
    dart (edgeOfDart d) (dartNegative d) = d := by
  cases d <;> rfl

/-- A signed relabeling whose reversal bit is the displayed dart orientation sends that dart to
the positive orientation of its renamed edge. -/
@[simp]
theorem signedRelabeling_mapDart_dart_self {α β : Type*}
    (edgeEquiv : α ≃ β) (reverse : α → Bool)
    (a : α) :
    (signedRelabeling edgeEquiv reverse).mapDart
        (dart a (reverse a)) =
      .pos (edgeEquiv a) := by
  cases hnegative : reverse a <;>
    simp [signedRelabeling, EdgeRelabeling.mapDart,
      dart, hnegative]

/-- The opposite displayed orientation is normalized to the negative renamed dart. -/
@[simp]
theorem signedRelabeling_mapDart_dart_not_self {α β : Type*}
    (edgeEquiv : α ≃ β) (reverse : α → Bool)
    (a : α) :
    (signedRelabeling edgeEquiv reverse).mapDart
        (dart a (!(reverse a))) =
      .neg (edgeEquiv a) := by
  cases hnegative : reverse a <;>
    simp [signedRelabeling, EdgeRelabeling.mapDart,
      dart, hnegative]

/-- Exact signed spelling of one boundary loop before final edge-name and sign normalization. -/
def boundaryLoopWord {α : Type*}
    (carrier hole : α)
    (carrierNegative holeNegative : Bool) :
    List (SignedDart α) :=
  [dart carrier carrierNegative,
    dart hole holeNegative,
    dart carrier (!carrierNegative)]

/-- Independent sign normalization sends an arbitrary boundary-loop spelling to the positive
carrier, positive hole, negative carrier convention used by the canonical representatives. -/
theorem map_boundaryLoopWord_normalized {α β : Type*}
    (edgeEquiv : α ≃ β) (reverse : α → Bool)
    (carrier hole : α)
    (carrierNegative holeNegative : Bool)
    (hcarrier : reverse carrier = carrierNegative)
    (hhole : reverse hole = holeNegative) :
    (boundaryLoopWord carrier hole
        carrierNegative holeNegative).map
          (signedRelabeling edgeEquiv reverse).mapDart =
      [.pos (edgeEquiv carrier), .pos (edgeEquiv hole),
        .neg (edgeEquiv carrier)] := by
  subst carrierNegative
  subst holeNegative
  simp [boundaryLoopWord]

/-- Ordinary surface validity reflects through a P1 expansion. -/
theorem isSurfaceValid_of_p1Expand
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validExpand : (P1.expand P a).IsSurfaceValid) :
    P.IsSurfaceValid := by
  refine
    ⟨(P1.faceEquiv P a).nonempty_congr.mpr
        validExpand.1,
      ?_, ?_, ?_⟩
  · intro face hboundary
    apply validExpand.2.1
      (P1.faceEquiv P a face)
    rw [P1.expand_boundary, hboundary]
    rfl
  · intro firstFace secondFace hrotated
    apply (P1.faceEquiv P a).injective
    apply validExpand.2.2.1
    rw [P1.expand_boundary, P1.expand_boundary]
    exact
      (P1.expandWord_isRotated_iff a
        (P.boundary firstFace)
        (P.boundary secondFace)).mpr hrotated
  · intro edge
    have hmultiplicity :=
      validExpand.2.2.2 edge.castSucc
    rw [← P1.edgeMultiplicity_expand_castSucc
      P a edge] at hmultiplicity
    exact hmultiplicity

/-- Unoriented edge count is the sum of its positive and negative dart counts. -/
theorem count_edgeOfDart_eq_pos_add_neg {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) :
    (word.map edgeOfDart).count a =
      word.count (.pos a) + word.count (.neg a) := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos e =>
          by_cases hea : e = a
          · subst e
            simp [edgeOfDart, ih]
            omega
          · simp [edgeOfDart, ih, hea]
      | neg e =>
          by_cases hea : e = a
          · subst e
            simp [edgeOfDart, ih]
            omega
          · simp [edgeOfDart, ih, hea]

/-- The four occurrence patterns allowed for one edge of a valid one-face word. -/
inductive EdgePattern {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
  | boundary
      (total : (word.map edgeOfDart).count a = 1)
  | positiveCrosscap
      (positive : word.count (.pos a) = 2)
      (negative : word.count (.neg a) = 0)
  | negativeCrosscap
      (positive : word.count (.pos a) = 0)
      (negative : word.count (.neg a) = 2)
  | opposite
      (positive : word.count (.pos a) = 1)
      (negative : word.count (.neg a) = 1)

/-- Every edge name actually used by a residual word still has a surface multiplicity.  Unlike
`IsSurfaceValid`, this predicate permits the ambient `Fin` type to contain already-grouped edge
names which no longer occur in the residual word. -/
def HasValidUsedMultiplicities {n : ℕ}
    (word : List (SignedDart (Fin n))) : Prop :=
  ∀ a, a ∈ word.map edgeOfDart →
    (word.map edgeOfDart).count a = 1 ∨
      (word.map edgeOfDart).count a = 2

/-- Ordinary one-face validity implies valid multiplicity for every used edge. -/
theorem hasValidUsedMultiplicities_of_isSurfaceValid {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    HasValidUsedMultiplicities word := by
  intro a _ha
  simpa only [Dyck.oneFace_edgeMultiplicity] using valid.2.2.2 a

/-- Residual surface multiplicities force the edge of a displayed inverse pair to occur nowhere
else in its tail. -/
theorem cancellablePair_edge_not_mem_tail_of_usedMultiplicities {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (multiplicities : HasValidUsedMultiplicities word) :
    pair.edge ∉ pair.tail.map edgeOfDart := by
  have hcount :
      (word.map edgeOfDart).count pair.edge =
        2 + (pair.tail.map edgeOfDart).count pair.edge := by
    have hrotatedCount :=
      (pair.rotated.map edgeOfDart).perm.count_eq pair.edge
    rw [hrotatedCount]
    cases pair.negativeFirst <;>
      simp [inversePair, edgeOfDart] <;>
      omega
  have hedge : pair.edge ∈ word.map edgeOfDart :=
    List.count_pos_iff.mp (by rw [hcount]; omega)
  have hmultiplicity := multiplicities pair.edge hedge
  intro htail
  have hpositive :
      0 < (pair.tail.map edgeOfDart).count pair.edge :=
    List.count_pos_iff.mpr htail
  omega

/-- Deleting a displayed inverse pair preserves the count of every edge which remains in the
tail. -/
theorem cancellablePair_count_tail_of_mem {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (multiplicities : HasValidUsedMultiplicities word)
    (e : Fin n)
    (he : e ∈ pair.tail.map edgeOfDart) :
    (word.map edgeOfDart).count e =
      (pair.tail.map edgeOfDart).count e := by
  have hpairAbsent :=
    cancellablePair_edge_not_mem_tail_of_usedMultiplicities
      pair multiplicities
  have hne : pair.edge ≠ e := by
    intro h
    subst e
    exact hpairAbsent he
  have hcount :=
    (pair.rotated.map edgeOfDart).perm.count_eq e
  cases hnegative : pair.negativeFirst <;>
    simp only [inversePair, hnegative, List.cons_append, List.nil_append, List.map_cons,
      edgeOfDart_pos, edgeOfDart_neg, ne_eq, hne, not_false_eq_true,
      List.count_cons_of_ne] at hcount <;>
    exact hcount

/-- Residual surface multiplicities survive deletion of a displayed inverse pair. -/
theorem cancellablePair_hasValidUsedMultiplicities_tail {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (multiplicities : HasValidUsedMultiplicities word) :
    HasValidUsedMultiplicities pair.tail := by
  intro e he
  rw [← cancellablePair_count_tail_of_mem
    pair multiplicities e he]
  apply multiplicities e
  exact List.count_pos_iff.mp
    (by
      rw [cancellablePair_count_tail_of_mem
        pair multiplicities e he]
      exact List.count_pos_iff.mpr he)

/-- Proof-relevant trace of the residual inverse-pair recursion.  Keeping the selected pair at
each step is essential when the same reduction is later lifted through an ambient marked word:
the erased residual endpoint alone does not say which protected token interval the pair crossed. -/
inductive ResidualPairReductionTrace {n : ℕ} :
    List (SignedDart (Fin n)) →
      List (SignedDart (Fin n)) → Type
  | done {word : List (SignedDart (Fin n))}
      (reduced : IsPairReduced word) :
      ResidualPairReductionTrace word word
  | cancel {word target : List (SignedDart (Fin n))}
      (pair : CancellablePair word)
      (tail : ResidualPairReductionTrace pair.tail target) :
      ResidualPairReductionTrace word target

/-- Certified result of repeatedly deleting adjacent inverse pairs from a residual word.  The
ambient edge type is intentionally retained: names belonging to already-extracted blocks may be
absent from both the input and output residual words.  Its trace records the exact recursion
choices for subsequent marked execution. -/
structure ResidualPairReduction {n : ℕ}
    (sourceWord : List (SignedDart (Fin n))) where
  /-- The `reducedWord` declaration. -/
  reducedWord : List (SignedDart (Fin n))
  /-- The `trace` declaration. -/
  trace :
    ResidualPairReductionTrace sourceWord reducedWord
  multiplicities : HasValidUsedMultiplicities reducedWord
  reduced : IsPairReduced reducedWord
  count_eq_of_mem :
    ∀ e, e ∈ reducedWord.map edgeOfDart →
      (sourceWord.map edgeOfDart).count e =
        (reducedWord.map edgeOfDart).count e
  length_le : reducedWord.length ≤ sourceWord.length

namespace ResidualPairReductionTrace

/-- The endpoint recorded by a residual cancellation trace is pair-reduced. -/
theorem target_isPairReduced {n : ℕ}
    {source target : List (SignedDart (Fin n))}
    (trace : ResidualPairReductionTrace source target) :
    IsPairReduced target := by
  induction trace with
  | done reduced =>
      exact reduced
  | cancel _ _ ih =>
      exact ih

/-- Residual cancellation never increases word length. -/
theorem target_length_le {n : ℕ}
    {source target : List (SignedDart (Fin n))}
    (trace : ResidualPairReductionTrace source target) :
    target.length ≤ source.length := by
  induction trace with
  | done =>
      exact le_rfl
  | @cancel word target pair tail ih =>
      have hlength := pair.rotated.perm.length_eq
      have hsource :
          word.length = 2 + pair.tail.length := by
        cases hnegative : pair.negativeFirst
        · have hsource' :
              word.length = pair.tail.length + 1 + 1 := by
            simpa [inversePair, hnegative] using hlength
          omega
        · have hsource' :
              word.length = pair.tail.length + 1 + 1 := by
            simpa [inversePair, hnegative] using hlength
          omega
      omega

end ResidualPairReductionTrace

/-- Fuel-bounded residual inverse-pair cancellation. -/
noncomputable def reduceResidualPairsFuel (fuel : ℕ) {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word) :
    word.length ≤ fuel → ResidualPairReduction word := by
  classical
  intro hbound
  by_cases hpairs : Nonempty (CancellablePair word)
  · let pair := Classical.choice hpairs
    have hlength :
        word.length = 2 + pair.tail.length := by
      have hrotatedLength := pair.rotated.perm.length_eq
      cases hnegative : pair.negativeFirst
      · have hrotatedLength' :
            word.length = pair.tail.length + 1 + 1 := by
          simpa [inversePair, hnegative] using hrotatedLength
        omega
      · have hrotatedLength' :
            word.length = pair.tail.length + 1 + 1 := by
          simpa [inversePair, hnegative] using hrotatedLength
        omega
    have hfuelPositive : 0 < fuel := by
      omega
    have htailBound : pair.tail.length ≤ fuel - 1 := by
      omega
    let tailMultiplicities :=
      cancellablePair_hasValidUsedMultiplicities_tail
        pair multiplicities
    let result :=
      reduceResidualPairsFuel (fuel - 1)
        pair.tail tailMultiplicities htailBound
    exact
      { reducedWord := result.reducedWord
        trace := .cancel pair result.trace
        multiplicities := result.multiplicities
        reduced := result.reduced
        count_eq_of_mem := by
          intro e he
          have htail :
              e ∈ pair.tail.map edgeOfDart := by
            apply List.count_pos_iff.mp
            rw [result.count_eq_of_mem e he]
            exact List.count_pos_iff.mpr he
          exact
            (cancellablePair_count_tail_of_mem
              pair multiplicities e htail).trans
              (result.count_eq_of_mem e he)
        length_le := by
          exact result.length_le.trans (by omega) }
  · exact
      { reducedWord := word
        trace := .done ⟨fun pair ↦ hpairs ⟨pair⟩⟩
        multiplicities := multiplicities
        reduced := ⟨fun pair ↦ hpairs ⟨pair⟩⟩
        count_eq_of_mem := by
          intro _ _
          rfl
        length_le := le_refl _ }
termination_by fuel
decreasing_by
  apply Nat.sub_lt
  · exact hfuelPositive
  · omega

/-- Repeatedly delete every adjacent inverse pair from a residual word while retaining its ambient
edge namespace and the surface multiplicities of all surviving names. -/
noncomputable def reduceResidualPairs {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word) :
    ResidualPairReduction word :=
  reduceResidualPairsFuel word.length word multiplicities (le_refl _)

namespace ResidualPairReduction

/-- Every name surviving residual cancellation occurred in the input residual word. -/
theorem mem_source_of_mem {n : ℕ}
    {sourceWord : List (SignedDart (Fin n))}
    (result : ResidualPairReduction sourceWord)
    (e : Fin n)
    (he : e ∈ result.reducedWord.map edgeOfDart) :
    e ∈ sourceWord.map edgeOfDart := by
  apply List.count_pos_iff.mp
  rw [result.count_eq_of_mem e he]
  exact List.count_pos_iff.mpr he

end ResidualPairReduction

/-- A known surface multiplicity classifies the two signed counts of an edge. -/
theorem exists_edgePattern_of_multiplicity {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hmultiplicity :
      (word.map edgeOfDart).count a = 1 ∨
        (word.map edgeOfDart).count a = 2) :
    Nonempty (EdgePattern word a) := by
  rcases hmultiplicity with hone | htwo
  · exact ⟨.boundary hone⟩
  · have hsum :
        word.count (.pos a) + word.count (.neg a) = 2 := by
      rw [← count_edgeOfDart_eq_pos_add_neg]
      exact htwo
    by_cases hpositive : word.count (.pos a) = 2
    · exact ⟨.positiveCrosscap hpositive (by omega)⟩
    · by_cases hnegative : word.count (.neg a) = 2
      · exact ⟨.negativeCrosscap (by omega) hnegative⟩
      · exact ⟨.opposite (by omega) (by omega)⟩

/-- Surface validity classifies every edge as boundary, equally oriented, or oppositely
oriented. -/
theorem exists_edgePattern {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (a : Fin n) :
    Nonempty (EdgePattern word a) :=
  exists_edgePattern_of_multiplicity word a (by
    simpa only [Dyck.oneFace_edgeMultiplicity] using valid.2.2.2 a)

/-- A list in which `a` occurs exactly once can be split at that occurrence, with certified
absence on both sides. -/
theorem exists_decomposition_of_count_eq_one {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hcount : (word.map edgeOfDart).count a = 1) :
    ∃ (negative : Bool) (left right : List (SignedDart (Fin n))),
      word = left ++ dart a negative :: right ∧
        a ∉ left.map edgeOfDart ∧
        a ∉ right.map edgeOfDart := by
  have hmem : a ∈ word.map edgeOfDart :=
    List.count_pos_iff.mp (by omega)
  rcases Reduction.exists_dart_of_mem_map_edgeOfDart hmem with
    ⟨d, hdword, hdedge⟩
  rw [List.mem_iff_append] at hdword
  rcases hdword with ⟨left, right, hword⟩
  have hleftCount : (left.map edgeOfDart).count a = 0 := by
    rw [hword] at hcount
    simp only [List.map_append, List.map_cons, List.count_append,
      List.count_cons] at hcount
    rw [hdedge] at hcount
    simp only [beq_self_eq_true, if_true] at hcount
    omega
  have hrightCount : (right.map edgeOfDart).count a = 0 := by
    rw [hword] at hcount
    simp only [List.map_append, List.map_cons, List.count_append,
      List.count_cons] at hcount
    rw [hdedge] at hcount
    simp only [beq_self_eq_true, if_true] at hcount
    omega
  have hleft : a ∉ left.map edgeOfDart :=
    List.count_eq_zero.mp hleftCount
  have hright : a ∉ right.map edgeOfDart :=
    List.count_eq_zero.mp hrightCount
  cases d with
  | pos e =>
      change e = a at hdedge
      subst e
      exact ⟨false, left, right, hword, hleft, hright⟩
  | neg e =>
      change e = a at hdedge
      subst e
      exact ⟨true, left, right, hword, hleft, hright⟩

/-- Cyclic data exposing the two occurrences of a twice-used edge. -/
structure DoubleOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  /-- The `firstNegative` declaration. -/
  firstNegative : Bool
  /-- The `secondNegative` declaration. -/
  secondNegative : Bool
  /-- The `between` declaration. -/
  between : List (SignedDart (Fin n))
  /-- The `remainder` declaration. -/
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (dart a firstNegative :: between ++
        dart a secondNegative :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- Every edge of multiplicity two in a one-face word has a certified cyclic two-occurrence
decomposition. -/
theorem exists_doubleOccurrenceForm_of_count_eq_two {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hcount : (word.map edgeOfDart).count a = 2) :
    Nonempty (DoubleOccurrenceForm word a) := by
  have hmem : a ∈ word.map edgeOfDart :=
    List.count_pos_iff.mp (by omega)
  rcases Reduction.exists_dart_of_mem_map_edgeOfDart hmem with
    ⟨first, hfirstWord, hfirstEdge⟩
  rw [List.mem_iff_append] at hfirstWord
  rcases hfirstWord with ⟨left, right, hword⟩
  let cyclicRemainder := right ++ left
  have hcyclicCount :
      (cyclicRemainder.map edgeOfDart).count a = 1 := by
    rw [hword] at hcount
    simp only [List.map_append, List.map_cons, List.count_append,
      List.count_cons] at hcount
    rw [hfirstEdge] at hcount
    simp only [beq_self_eq_true, if_true] at hcount
    simp only [cyclicRemainder, List.map_append, List.count_append]
    omega
  rcases exists_decomposition_of_count_eq_one
      cyclicRemainder a hcyclicCount with
    ⟨secondNegative, between, remainder,
      hcyclic, hbetween, hremainder⟩
  have hrotation :
      word.IsRotated (first :: cyclicRemainder) := by
    rw [hword]
    simpa only [List.cons_append, List.append_assoc,
      cyclicRemainder] using
      (List.isRotated_append
        (l := left) (l' := first :: right))
  rw [hcyclic] at hrotation
  cases first with
  | pos e =>
      change e = a at hfirstEdge
      subst e
      exact ⟨
        { firstNegative := false
          secondNegative := secondNegative
          between := between
          remainder := remainder
          rotated := by
            simpa [dart, List.cons_append,
              List.append_assoc] using hrotation
          edge_not_mem_between := hbetween
          edge_not_mem_remainder := hremainder }⟩
  | neg e =>
      change e = a at hfirstEdge
      subst e
      exact ⟨
        { firstNegative := true
          secondNegative := secondNegative
          between := between
          remainder := remainder
          rotated := by
            simpa [dart, List.cons_append,
              List.append_assoc] using hrotation
          edge_not_mem_between := hbetween
          edge_not_mem_remainder := hremainder }⟩

/-- Surface validity supplies a double-occurrence form for every twice-used edge. -/
noncomputable def doubleOccurrenceFormOfMultiplicityTwo {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (_valid : (Dyck.oneFace word).IsSurfaceValid)
    (a : Fin n)
    (htwo : (Dyck.oneFace word).edgeMultiplicity a = 2) :
    DoubleOccurrenceForm word a :=
  Classical.choice
    (exists_doubleOccurrenceForm_of_count_eq_two word a
      (by simpa only [Dyck.oneFace_edgeMultiplicity] using htwo))

/-- In a pair-reduced word, oppositely oriented occurrences cannot be cyclically adjacent. -/
theorem DoubleOccurrenceForm.between_ne_nil_of_opposite {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : DoubleOccurrenceForm word a)
    (reduced : IsPairReduced word)
    (hopposite : form.firstNegative ≠ form.secondNegative) :
    form.between ≠ [] := by
  intro hbetween
  rcases reduced with ⟨hreduced⟩
  apply hreduced
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  · exact (hopposite (hfirst.trans hsecond.symm)).elim
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := false
        rotated := by
          simpa [inversePair, dart, hfirst, hsecond,
            hbetween] using form.rotated }
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := true
        rotated := by
          simpa [inversePair, dart, hfirst, hsecond,
            hbetween] using form.rotated }
  · exact (hopposite (hfirst.trans hsecond.symm)).elim

/-- A twice-used edge displayed with equal orientations. -/
structure CrosscapOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  /-- The `negative` declaration. -/
  negative : Bool
  /-- The `between` declaration. -/
  between : List (SignedDart (Fin n))
  /-- The `remainder` declaration. -/
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (dart a negative :: between ++
        dart a negative :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- An oppositely used edge displayed positive first and negative second. -/
structure OppositeOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  /-- The `between` declaration. -/
  between : List (SignedDart (Fin n))
  /-- The `remainder` declaration. -/
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (.pos a :: between ++ .neg a :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- An orientation-symmetric directed arc between the two opposite occurrences of an edge.
Unlike `OppositeOccurrenceForm`, this form permits either sign at the beginning, which is the
right induction invariant when descending to a shorter nested pair. -/
structure OppositeArcForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  /-- The `firstNegative` declaration. -/
  firstNegative : Bool
  /-- The `between` declaration. -/
  between : List (SignedDart (Fin n))
  /-- The `remainder` declaration. -/
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (dart a firstNegative :: between ++
        dart a (!firstNegative) :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- Forget the positive-first convention of an opposite occurrence form. -/
def OppositeOccurrenceForm.toArc {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeOccurrenceForm word a) :
    OppositeArcForm word a where
  firstNegative := false
  between := form.between
  remainder := form.remainder
  rotated := by
    simpa [dart] using form.rotated
  edge_not_mem_between := form.edge_not_mem_between
  edge_not_mem_remainder := form.edge_not_mem_remainder

/-- Pair reduction makes the directed interval of every opposite arc nonempty. -/
theorem OppositeArcForm.between_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (reduced : IsPairReduced word) :
    form.between ≠ [] := by
  intro hbetween
  rcases reduced with ⟨hreduced⟩
  apply hreduced
  cases horientation : form.firstNegative
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := false
        rotated := by
          simpa [inversePair, dart, horientation,
            hbetween] using form.rotated }
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := true
        rotated := by
          simpa [inversePair, dart, horientation,
            hbetween] using form.rotated }

/-- Two oppositely oriented edge pairs whose endpoints interleave cyclically.  The first
distinguished pair is displayed positive then negative.  The Boolean records whether the
occurrence of `b` inside that pair is negative; a signed relabeling will reverse `b` when
necessary before applying handle extraction. -/
structure InterleavedOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a b : Fin n) where
  /-- The `bNegativeInside` declaration. -/
  bNegativeInside : Bool
  /-- The `beforeB` declaration. -/
  beforeB : List (SignedDart (Fin n))
  /-- The `beforeNegA` declaration. -/
  beforeNegA : List (SignedDart (Fin n))
  /-- The `beforeOutsideB` declaration. -/
  beforeOutsideB : List (SignedDart (Fin n))
  /-- The `remainder` declaration. -/
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (.pos a :: beforeB ++
        dart b bNegativeInside :: beforeNegA ++
        .neg a :: beforeOutsideB ++
        dart b (!bNegativeInside) :: remainder)
  edge_ne : a ≠ b
  a_not_mem_beforeB : a ∉ beforeB.map edgeOfDart
  a_not_mem_beforeNegA : a ∉ beforeNegA.map edgeOfDart
  a_not_mem_beforeOutsideB : a ∉ beforeOutsideB.map edgeOfDart
  a_not_mem_remainder : a ∉ remainder.map edgeOfDart
  b_not_mem_beforeB : b ∉ beforeB.map edgeOfDart
  b_not_mem_beforeNegA : b ∉ beforeNegA.map edgeOfDart
  b_not_mem_beforeOutsideB : b ∉ beforeOutsideB.map edgeOfDart
  b_not_mem_remainder : b ∉ remainder.map edgeOfDart

/-- A positive crosscap edge has an equally oriented occurrence form. -/
theorem exists_positiveCrosscapOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hpositive : word.count (.pos a) = 2)
    (hnegative : word.count (.neg a) = 0) :
    Nonempty (CrosscapOccurrenceForm word a) := by
  have htotal : (word.map edgeOfDart).count a = 2 := by
    rw [count_edgeOfDart_eq_pos_add_neg, hpositive, hnegative]
  rcases exists_doubleOccurrenceForm_of_count_eq_two
      word a htotal with ⟨form⟩
  have hcount :=
    form.rotated.perm.count_eq (.neg a)
  rw [hnegative] at hcount
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  · exact ⟨
      { negative := false
        between := form.between
        remainder := form.remainder
        rotated := by
          simpa [dart, hfirst, hsecond] using form.rotated
        edge_not_mem_between := form.edge_not_mem_between
        edge_not_mem_remainder := form.edge_not_mem_remainder }⟩
  all_goals
    simp [dart, hfirst, hsecond] at hcount

/-- A negative crosscap edge has an equally oriented occurrence form. -/
theorem exists_negativeCrosscapOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hpositive : word.count (.pos a) = 0)
    (hnegative : word.count (.neg a) = 2) :
    Nonempty (CrosscapOccurrenceForm word a) := by
  have htotal : (word.map edgeOfDart).count a = 2 := by
    rw [count_edgeOfDart_eq_pos_add_neg, hpositive, hnegative]
  rcases exists_doubleOccurrenceForm_of_count_eq_two
      word a htotal with ⟨form⟩
  have hcount :=
    form.rotated.perm.count_eq (.pos a)
  rw [hpositive] at hcount
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  all_goals try
    simp [dart, hfirst, hsecond] at hcount
  exact ⟨
    { negative := true
      between := form.between
      remainder := form.remainder
      rotated := by
        simpa [dart, hfirst, hsecond] using form.rotated
      edge_not_mem_between := form.edge_not_mem_between
      edge_not_mem_remainder := form.edge_not_mem_remainder }⟩

/-- An opposite edge has a cyclic spelling with its positive occurrence first. -/
theorem exists_oppositeOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hpositive : word.count (.pos a) = 1)
    (hnegative : word.count (.neg a) = 1) :
    Nonempty (OppositeOccurrenceForm word a) := by
  have htotal : (word.map edgeOfDart).count a = 2 := by
    rw [count_edgeOfDart_eq_pos_add_neg, hpositive, hnegative]
  rcases exists_doubleOccurrenceForm_of_count_eq_two
      word a htotal with ⟨form⟩
  have hposCount :=
    form.rotated.perm.count_eq (.pos a)
  have hnegCount :=
    form.rotated.perm.count_eq (.neg a)
  rw [hpositive] at hposCount
  rw [hnegative] at hnegCount
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  · simp [dart, hfirst, hsecond] at hposCount
  · exact ⟨
      { between := form.between
        remainder := form.remainder
        rotated := by
          simpa [dart, hfirst, hsecond] using form.rotated
        edge_not_mem_between := form.edge_not_mem_between
        edge_not_mem_remainder := form.edge_not_mem_remainder }⟩
  · refine ⟨
      { between := form.remainder
        remainder := form.between
        rotated := ?_
        edge_not_mem_between := form.edge_not_mem_remainder
        edge_not_mem_remainder := form.edge_not_mem_between }⟩
    have hrotateAgain :
        (dart a form.firstNegative :: form.between ++
          dart a form.secondNegative :: form.remainder).IsRotated
            (.pos a :: form.remainder ++
              .neg a :: form.between) := by
      convert
        (List.isRotated_append
          (l := .neg a :: form.between)
          (l' := .pos a :: form.remainder)) using 1
      all_goals
        simp [dart, hfirst, hsecond, List.cons_append]
    exact form.rotated.trans hrotateAgain
  · simp [dart, hfirst, hsecond] at hnegCount

/-- A once-used boundary edge displayed at the cyclic head. -/
structure BoundaryOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  /-- The `negative` declaration. -/
  negative : Bool
  /-- The `remainder` declaration. -/
  remainder : List (SignedDart (Fin n))
  rotated : word.IsRotated (dart a negative :: remainder)
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- A pairing feature on which the normalization recursion can immediately act. -/
inductive ActionablePairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
  | boundary (a : Fin n) (form : BoundaryOccurrenceForm word a)
  | crosscap (a : Fin n) (form : CrosscapOccurrenceForm word a)
  | handle (a b : Fin n) (form : InterleavedOccurrenceForm word a b)

namespace ActionablePairReductionFeature

/-- Delete the darts of the extracted block, retaining the exact residual order produced by the
proof-generating rewrite endpoint. -/
def residualWord {n : ℕ} {word : List (SignedDart (Fin n))} :
    ActionablePairReductionFeature word →
      List (SignedDart (Fin n))
  | .boundary _ form =>
      form.remainder
  | .crosscap _ form =>
      inverseWord form.remainder ++ form.between
  | .handle _ _ form =>
      form.remainder ++ form.beforeOutsideB ++
        form.beforeNegA ++ form.beforeB

/-- Every actionable extraction strictly shortens its residual word. -/
theorem residualWord_length_lt {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.residualWord.length < word.length := by
  cases feature with
  | boundary a form =>
      have hlength := form.rotated.perm.length_eq
      simp only [residualWord, List.length_cons] at hlength ⊢
      omega
  | crosscap a form =>
      have hlength := form.rotated.perm.length_eq
      simp only [residualWord, List.length_append,
        inverseWord_length, List.length_cons] at hlength ⊢
      omega
  | handle a b form =>
      have hlength := form.rotated.perm.length_eq
      simp only [residualWord, List.length_append,
        List.length_cons] at hlength ⊢
      omega

/-- Counts of every edge still used by the residual word agree with their counts in the source
word. -/
theorem count_residualWord_of_mem {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (e : Fin n)
    (he : e ∈ feature.residualWord.map edgeOfDart) :
    (word.map edgeOfDart).count e =
      (feature.residualWord.map edgeOfDart).count e := by
  cases feature with
  | boundary a form =>
      have hae : a ≠ e := by
        intro h
        subst e
        exact form.edge_not_mem_remainder he
      have hcount :=
        (form.rotated.map edgeOfDart).perm.count_eq e
      simp only [residualWord, List.map_cons,
        edgeOfDart_dart, List.count_cons] at hcount ⊢
      simp only [beq_iff_eq, hae, ↓reduceIte, add_zero] at hcount
      exact hcount
  | crosscap a form =>
      have haResidual :
          a ∉ (inverseWord form.remainder ++
            form.between).map edgeOfDart := by
        simp [map_edgeOfDart_inverseWord,
          form.edge_not_mem_remainder,
          form.edge_not_mem_between]
      have hae : a ≠ e := by
        intro h
        subst e
        exact haResidual he
      have hcount :=
        (form.rotated.map edgeOfDart).perm.count_eq e
      simp only [residualWord, List.map_cons, List.map_append,
        edgeOfDart_dart, List.count_cons,
        List.count_append] at hcount ⊢
      rw [map_edgeOfDart_inverseWord, List.count_reverse]
      simp [hae] at hcount
      omega
  | handle a b form =>
      have haResidual :
          a ∉ (form.remainder ++ form.beforeOutsideB ++
            form.beforeNegA ++ form.beforeB).map edgeOfDart := by
        simp [form.a_not_mem_remainder,
          form.a_not_mem_beforeOutsideB,
          form.a_not_mem_beforeNegA,
          form.a_not_mem_beforeB]
      have hbResidual :
          b ∉ (form.remainder ++ form.beforeOutsideB ++
            form.beforeNegA ++ form.beforeB).map edgeOfDart := by
        simp [form.b_not_mem_remainder,
          form.b_not_mem_beforeOutsideB,
          form.b_not_mem_beforeNegA,
          form.b_not_mem_beforeB]
      have hae : a ≠ e := by
        intro h
        subst e
        exact haResidual he
      have hbe : b ≠ e := by
        intro h
        subst e
        exact hbResidual he
      have hcount :=
        (form.rotated.map edgeOfDart).perm.count_eq e
      simp only [residualWord, List.map_cons, List.map_append,
        edgeOfDart_pos, edgeOfDart_neg, edgeOfDart_dart,
        List.count_cons,
        List.count_append] at hcount ⊢
      simp [hae, hbe] at hcount
      omega

/-- Every edge name retained by an actionable feature occurred in its source word. -/
theorem mem_source_of_mem_residualWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (e : Fin n)
    (he : e ∈ feature.residualWord.map edgeOfDart) :
    e ∈ word.map edgeOfDart := by
  apply List.count_pos_iff.mp
  rw [feature.count_residualWord_of_mem e he]
  exact List.count_pos_iff.mpr he

/-- Used-edge surface multiplicities survive deletion of an extracted block. -/
theorem hasValidUsedMultiplicities_residualWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (multiplicities : HasValidUsedMultiplicities word) :
    HasValidUsedMultiplicities feature.residualWord := by
  intro e he
  rw [← feature.count_residualWord_of_mem e he]
  apply multiplicities e
  exact List.count_pos_iff.mp
    (by
      rw [feature.count_residualWord_of_mem e he]
      exact List.count_pos_iff.mpr he)

end ActionablePairReductionFeature

/-- Lower an edge name after moving a distinguished, unused name to the last position. -/
def Cancellation.lowerEdge {n : ℕ}
    (a e : Fin (n + 1)) (hne : e ≠ a) : Fin n :=
  (Cancellation.moveToLast a e).castPred (by
    intro hlast
    apply hne
    apply (Cancellation.moveToLast a).injective
    rw [hlast]
    simp [Cancellation.moveToLast])

@[simp]
theorem Cancellation.castSucc_lowerEdge {n : ℕ}
    (a e : Fin (n + 1)) (hne : e ≠ a) :
    (Cancellation.lowerEdge a e hne).castSucc =
      Cancellation.moveToLast a e := by
  simp [Cancellation.lowerEdge]

/-- Re-embed a lowered edge into the old namespace, undoing the move-to-last relabeling. -/
def Cancellation.restoreEdge {n : ℕ}
    (a : Fin (n + 1)) (e : Fin n) : Fin (n + 1) :=
  (Cancellation.moveToLast a).symm e.castSucc

@[simp]
theorem Cancellation.restoreEdge_lowerEdge {n : ℕ}
    (a e : Fin (n + 1)) (hne : e ≠ a) :
    Cancellation.restoreEdge a
        (Cancellation.lowerEdge a e hne) =
      e := by
  apply (Cancellation.moveToLast a).injective
  simp [Cancellation.restoreEdge]

/-- The `lowerDart` declaration. -/
@[simp]
def Cancellation.lowerDart {n : ℕ}
    (a : Fin (n + 1)) (d : SignedDart (Fin (n + 1)))
    (hne : edgeOfDart d ≠ a) : SignedDart (Fin n) :=
  match d with
  | .pos e => .pos (Cancellation.lowerEdge a e hne)
  | .neg e => .neg (Cancellation.lowerEdge a e hne)

/-- Re-embed a lowered dart into the old namespace. -/
def Cancellation.restoreDart {n : ℕ}
    (a : Fin (n + 1)) :
    SignedDart (Fin n) → SignedDart (Fin (n + 1))
  | .pos e => .pos (Cancellation.restoreEdge a e)
  | .neg e => .neg (Cancellation.restoreEdge a e)

theorem Cancellation.restoreDart_lowerDart {n : ℕ}
    (a : Fin (n + 1)) (d : SignedDart (Fin (n + 1)))
    (hne : edgeOfDart d ≠ a) :
    Cancellation.restoreDart a
        (Cancellation.lowerDart a d hne) =
      d := by
  cases d with
  | pos e =>
      exact congrArg SignedDart.pos
        (Cancellation.restoreEdge_lowerEdge a e hne)
  | neg e =>
      exact congrArg SignedDart.neg
        (Cancellation.restoreEdge_lowerEdge a e hne)

theorem Cancellation.restoreEdge_edgeOfDart_lowerDart {n : ℕ}
    (a : Fin (n + 1)) (d : SignedDart (Fin (n + 1)))
    (hne : edgeOfDart d ≠ a) :
    Cancellation.restoreEdge a
        (edgeOfDart
          (Cancellation.lowerDart a d hne)) =
      edgeOfDart d := by
  cases d with
  | pos e => exact Cancellation.restoreEdge_lowerEdge a e hne
  | neg e => exact Cancellation.restoreEdge_lowerEdge a e hne

@[simp]
theorem Cancellation.contractDart_mapEquiv_moveToLast {n : ℕ}
    (a : Fin (n + 1)) (d : SignedDart (Fin (n + 1)))
    (hne : edgeOfDart d ≠ a) :
    P1.contractDart
        (SignedDart.mapEquiv
          (Cancellation.moveToLast a) d) =
      some (Cancellation.lowerDart a d hne) := by
  cases d with
  | pos e =>
      change
        P1.contractDart
            (.pos (Cancellation.moveToLast a e)) =
          some (.pos (Cancellation.lowerEdge a e hne))
      have hmove :
          Cancellation.moveToLast a e =
            (Cancellation.lowerEdge a e hne).castSucc :=
        (Cancellation.castSucc_lowerEdge a e hne).symm
      rw [hmove, P1.contractDart_pos_castSucc]
  | neg e =>
      change
        P1.contractDart
            (.neg (Cancellation.moveToLast a e)) =
          some (.neg (Cancellation.lowerEdge a e hne))
      have hmove :
          Cancellation.moveToLast a e =
            (Cancellation.lowerEdge a e hne).castSucc :=
        (Cancellation.castSucc_lowerEdge a e hne).symm
      rw [hmove, P1.contractDart_neg_castSucc]

/-- Lower a word which avoids a distinguished edge, preserving its exact dart order. -/
def Cancellation.lowerWordAvoiding {n : ℕ}
    (a : Fin (n + 1)) :
    (word : List (SignedDart (Fin (n + 1)))) →
      a ∉ word.map edgeOfDart →
      List (SignedDart (Fin n))
  | [], _ => []
  | d :: word, ha =>
      Cancellation.lowerDart a d (by
        intro hedge
        apply ha
        simp [hedge]) ::
        Cancellation.lowerWordAvoiding a word (by
          intro htail
          apply ha
          simp [htail])

/-- Lowering a word explicitly agrees with moving the removed name last and applying P1
contraction. -/
theorem Cancellation.lowerWordAvoiding_eq_lowerTail {n : ℕ}
    (a : Fin (n + 1))
    (word : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ word.map edgeOfDart) :
    Cancellation.lowerWordAvoiding a word ha =
      Cancellation.lowerTail a word := by
  induction word with
  | nil =>
      rfl
  | cons d word ih =>
      have hd : edgeOfDart d ≠ a := by
        intro hedge
        apply ha
        simp [hedge]
      have htail : a ∉ word.map edgeOfDart := by
        intro hmem
        apply ha
        simp [hmem]
      simp only [Cancellation.lowerWordAvoiding,
        Cancellation.lowerTail, Cancellation.renamedTail,
        List.map_cons, P1.contractWord, List.filterMap_cons]
      rw [Cancellation.contractDart_mapEquiv_moveToLast
        a d hd]
      simp only [List.cons.injEq, true_and]
      exact ih htail

/-- Removing an absent ambient edge name does not turn a nonempty word into the empty word. -/
theorem Cancellation.lowerTail_ne_nil_of_ne_nil {n : ℕ}
    (a : Fin (n + 1))
    (word : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ word.map edgeOfDart)
    (hne : word ≠ []) :
    Cancellation.lowerTail a word ≠ [] := by
  intro hlower
  have hretained :=
    Cancellation.retainWord_lowerTail a word ha
  rw [hlower] at hretained
  have hrenamed :
      Cancellation.renamedTail a word = [] := by
    simpa using hretained.symm
  apply hne
  simpa [Cancellation.renamedTail] using hrenamed

/-- Re-embedding all names in a lowered word recovers the source edge-name list exactly. -/
theorem Cancellation.restoreEdges_lowerTail {n : ℕ}
    (a : Fin (n + 1))
    (word : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ word.map edgeOfDart) :
    ((Cancellation.lowerTail a word).map
        edgeOfDart).map (Cancellation.restoreEdge a) =
      word.map edgeOfDart := by
  rw [← Cancellation.lowerWordAvoiding_eq_lowerTail
    a word ha]
  induction word with
  | nil =>
      rfl
  | cons d word ih =>
      have htail : a ∉ word.map edgeOfDart := by
        intro hmem
        apply ha
        simp [hmem]
      simp only [Cancellation.lowerWordAvoiding,
        List.map_cons, List.cons.injEq]
      constructor
      · exact
          Cancellation.restoreEdge_edgeOfDart_lowerDart
            a d _
      · exact ih htail

/-- The combinatorial block contributed by one actionable extraction.  Orientations on boundary
and crosscap blocks are retained until the final signed relabeling; handle extraction has already
normalized both distinguished edge orientations. -/
inductive ExtractedBlock (n : ℕ)
  | boundary (a : Fin n) (negative : Bool)
  | crosscap (a : Fin n) (negative : Bool)
  | handle (a b : Fin n)

namespace ExtractedBlock

/-- Ambient edge names consumed by an extracted block. -/
def edges {n : ℕ} : ExtractedBlock n → List (Fin n)
  | .boundary a _ => [a]
  | .crosscap a _ => [a]
  | .handle a b => [a, b]

/-- Exact signed word contributed by an extracted block. -/
def word {n : ℕ} : ExtractedBlock n →
    List (SignedDart (Fin n))
  | .boundary a negative => [dart a negative]
  | .crosscap a negative =>
      [dart a negative, dart a negative]
  | .handle a b =>
      [.pos a, .pos b, .neg a, .neg b]

/-- Block obtained by reading an extracted block backwards with every dart reversed. -/
def inverse {n : ℕ} : ExtractedBlock n → ExtractedBlock n
  | .boundary a negative => .boundary a (!negative)
  | .crosscap a negative => .crosscap a (!negative)
  | .handle a b => .handle b a

/-- Relabel every ambient edge name in an extracted block. -/
def mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m) :
    ExtractedBlock n → ExtractedBlock m
  | .boundary a negative => .boundary (e a) negative
  | .crosscap a negative => .crosscap (e a) negative
  | .handle a b => .handle (e a) (e b)

/-- Remove an ambient edge name known not to occur in an extracted block. -/
def lowerAvoiding {n : ℕ} (a : Fin (n + 1))
    (block : ExtractedBlock (n + 1))
    (ha : a ∉ block.edges) : ExtractedBlock n :=
  match block with
  | .boundary e negative =>
      .boundary
        (Cancellation.lowerEdge a e (by
          intro hea
          subst e
          exact ha (by simp [edges])))
        negative
  | .crosscap e negative =>
      .crosscap
        (Cancellation.lowerEdge a e (by
          intro hea
          subst e
          exact ha (by simp [edges])))
        negative
  | .handle e f =>
      .handle
        (Cancellation.lowerEdge a e (by
          intro hea
          subst e
          exact ha (by simp [edges])))
        (Cancellation.lowerEdge a f (by
          intro hfa
          subst f
          exact ha (by simp [edges])))

@[simp]
theorem word_inverse {n : ℕ} (block : ExtractedBlock n) :
    block.inverse.word = inverseWord block.word := by
  cases block with
  | boundary a negative =>
      cases negative <;> rfl
  | crosscap a negative =>
      cases negative <;> rfl
  | handle a b =>
      rfl

@[simp]
theorem inverse_inverse {n : ℕ} (block : ExtractedBlock n) :
    block.inverse.inverse = block := by
  cases block with
  | boundary a negative =>
      cases negative <;> rfl
  | crosscap a negative =>
      cases negative <;> rfl
  | handle a b =>
      rfl

@[simp]
theorem edges_inverse {n : ℕ} (block : ExtractedBlock n) :
    block.inverse.edges = block.edges.reverse := by
  cases block <;> rfl

@[simp]
theorem word_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : ExtractedBlock n) :
    (block.mapEquiv e).word =
      block.word.map (SignedDart.mapEquiv e) := by
  cases block with
  | boundary a negative =>
      cases negative <;> rfl
  | crosscap a negative =>
      cases negative <;> rfl
  | handle =>
      rfl

@[simp]
theorem edges_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : ExtractedBlock n) :
    (block.mapEquiv e).edges = block.edges.map e := by
  cases block <;> rfl

@[simp]
theorem mem_map_edgeOfDart_word_iff {n : ℕ}
    (block : ExtractedBlock n) (a : Fin n) :
    a ∈ block.word.map edgeOfDart ↔ a ∈ block.edges := by
  cases block with
  | boundary edge negative =>
      cases negative <;> simp [word, edges]
  | crosscap edge negative =>
      cases negative <;> simp [word, edges]
  | handle first second =>
      simp [word, edges]
      tauto

@[simp]
theorem inverse_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : ExtractedBlock n) :
    (block.mapEquiv e).inverse =
      block.inverse.mapEquiv e := by
  cases block <;> rfl

/-- A boundary singleton is positive after reversing precisely its recorded input orientation. -/
theorem map_word_boundary_normalized {n : ℕ} {Edge : Type*}
    (edgeEquiv : Fin n ≃ Edge) (reverse : Fin n → Bool)
    (a : Fin n) (negative : Bool)
    (horientation : reverse a = negative) :
    ((boundary a negative).word.map
        (signedRelabeling edgeEquiv reverse).mapDart) =
      [.pos (edgeEquiv a)] := by
  subst negative
  simp [word]

/-- A crosscap square is positive after reversing precisely its recorded input orientation. -/
theorem map_word_crosscap_normalized {n : ℕ} {Edge : Type*}
    (edgeEquiv : Fin n ≃ Edge) (reverse : Fin n → Bool)
    (a : Fin n) (negative : Bool)
    (horientation : reverse a = negative) :
    ((crosscap a negative).word.map
        (signedRelabeling edgeEquiv reverse).mapDart) =
      [.pos (edgeEquiv a), .pos (edgeEquiv a)] := by
  subst negative
  simp [word]

/-- An extracted handle already has the canonical commutator orientation whenever neither of its
two edge names is reversed by the final signed relabeling. -/
theorem map_word_handle_normalized {n : ℕ} {Edge : Type*}
    (edgeEquiv : Fin n ≃ Edge) (reverse : Fin n → Bool)
    (a b : Fin n)
    (ha : reverse a = false) (hb : reverse b = false) :
    ((handle a b).word.map
        (signedRelabeling edgeEquiv reverse).mapDart) =
      [.pos (edgeEquiv a), .pos (edgeEquiv b),
        .neg (edgeEquiv a), .neg (edgeEquiv b)] := by
  simp [word, signedRelabeling,
    EdgeRelabeling.mapDart, ha, hb]

/-- Expanding a lowered block agrees with renaming its old spelling and contracting the unused
last edge. -/
theorem word_lowerAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (block : ExtractedBlock (n + 1))
    (ha : a ∉ block.edges) :
    (block.lowerAvoiding a ha).word =
      Cancellation.lowerTail a block.word := by
  have haWord : a ∉ block.word.map edgeOfDart := by
    simpa only [mem_map_edgeOfDart_word_iff] using ha
  rw [← Cancellation.lowerWordAvoiding_eq_lowerTail
    a block.word haWord]
  cases block with
  | boundary e negative =>
      cases negative <;>
        simp [lowerAvoiding, word,
          Cancellation.lowerWordAvoiding,
          Cancellation.lowerDart, dart]
  | crosscap e negative =>
      cases negative <;>
        simp [lowerAvoiding, word,
          Cancellation.lowerWordAvoiding,
          Cancellation.lowerDart, dart]
  | handle e f =>
      simp [lowerAvoiding, word,
        Cancellation.lowerWordAvoiding,
        Cancellation.lowerDart]

/-- Re-embedding the edge names of a lowered block recovers its original edge list. -/
theorem edges_lowerAvoiding_map_restoreEdge {n : ℕ}
    (a : Fin (n + 1))
    (block : ExtractedBlock (n + 1))
    (ha : a ∉ block.edges) :
    (block.lowerAvoiding a ha).edges.map
        (Cancellation.restoreEdge a) =
      block.edges := by
  cases block <;>
    simp [lowerAvoiding, edges]

/-- Concatenate a sequence of extracted blocks into its exact signed boundary word. -/
def sequenceWord {n : ℕ} (blocks : List (ExtractedBlock n)) :
    List (SignedDart (Fin n)) :=
  (blocks.map word).flatten

/-- Reverse a block sequence in the order induced by reversing its full signed word. -/
def inverseSequence {n : ℕ} (blocks : List (ExtractedBlock n)) :
    List (ExtractedBlock n) :=
  (blocks.map inverse).reverse

@[simp]
theorem sequenceWord_nil {n : ℕ} :
    sequenceWord ([] : List (ExtractedBlock n)) = [] :=
  rfl

@[simp]
theorem sequenceWord_cons {n : ℕ}
    (block : ExtractedBlock n)
    (blocks : List (ExtractedBlock n)) :
    sequenceWord (block :: blocks) =
      block.word ++ sequenceWord blocks := by
  simp [sequenceWord]

@[simp]
theorem sequenceWord_append {n : ℕ}
    (left right : List (ExtractedBlock n)) :
    sequenceWord (left ++ right) =
      sequenceWord left ++ sequenceWord right := by
  simp [sequenceWord]

@[simp]
theorem sequenceWord_inverseSequence {n : ℕ}
    (blocks : List (ExtractedBlock n)) :
    sequenceWord (inverseSequence blocks) =
      inverseWord (sequenceWord blocks) := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      have ih' :
          sequenceWord ((blocks.map inverse).reverse) =
            inverseWord (sequenceWord blocks) := by
        simpa only [inverseSequence] using ih
      simp [inverseSequence, inverseWord_append, ih']

end ExtractedBlock

/-- A completed normalization block.  Boundary singletons are absent: a boundary block enters
this type only after a residual carrier pair has closed it into the three-dart loop required by
the canonical representatives. -/
inductive CompletedBlock (n : ℕ)
  | crosscap (a : Fin n) (negative : Bool)
  | handle (a b : Fin n)
  | boundary (carrier hole : Fin n)
      (carrierNegative holeNegative : Bool)

namespace CompletedBlock

/-- Exact signed word represented by a completed block. -/
def word {n : ℕ} : CompletedBlock n →
    List (SignedDart (Fin n))
  | .crosscap a negative =>
      [dart a negative, dart a negative]
  | .handle a b =>
      [.pos a, .pos b, .neg a, .neg b]
  | .boundary carrier hole carrierNegative holeNegative =>
      boundaryLoopWord carrier hole
        carrierNegative holeNegative

/-- Ambient edge names used by a completed block. -/
def edges {n : ℕ} : CompletedBlock n → List (Fin n)
  | .crosscap a _ => [a]
  | .handle a b => [a, b]
  | .boundary carrier hole _ _ => [carrier, hole, carrier]

/-- Distinct-name spine of a completed block.  Unlike `edges`, this records a boundary carrier
once rather than once per dart occurrence. -/
def names {n : ℕ} : CompletedBlock n → List (Fin n)
  | .crosscap a _ => [a]
  | .handle a b => [a, b]
  | .boundary carrier hole _ _ => [carrier, hole]

/-- Reverse a completed block as one atomic cyclic-word segment. -/
def inverse {n : ℕ} : CompletedBlock n → CompletedBlock n
  | .crosscap a negative => .crosscap a (!negative)
  | .handle a b => .handle b a
  | .boundary carrier hole carrierNegative holeNegative =>
      .boundary carrier hole carrierNegative (!holeNegative)

/-- Relabel every edge of a completed block. -/
def mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m) :
    CompletedBlock n → CompletedBlock m
  | .crosscap a negative => .crosscap (e a) negative
  | .handle a b => .handle (e a) (e b)
  | .boundary carrier hole carrierNegative holeNegative =>
      .boundary (e carrier) (e hole)
        carrierNegative holeNegative

/-- Remove an ambient edge name known not to occur in a completed block. -/
def lowerAvoiding {n : ℕ} (a : Fin (n + 1))
    (block : CompletedBlock (n + 1))
    (ha : a ∉ block.edges) : CompletedBlock n :=
  match block with
  | .crosscap e negative =>
      .crosscap
        (Cancellation.lowerEdge a e (by
          intro hea
          subst e
          exact ha (by simp [edges])))
        negative
  | .handle e f =>
      .handle
        (Cancellation.lowerEdge a e (by
          intro hea
          subst e
          exact ha (by simp [edges])))
        (Cancellation.lowerEdge a f (by
          intro hfa
          subst f
          exact ha (by simp [edges])))
  | .boundary carrier hole carrierNegative holeNegative =>
      .boundary
        (Cancellation.lowerEdge a carrier (by
          intro hca
          subst carrier
          exact ha (by simp [edges])))
        (Cancellation.lowerEdge a hole (by
          intro hha
          subst hole
          exact ha (by simp [edges])))
        carrierNegative holeNegative

@[simp]
theorem word_inverse {n : ℕ} (block : CompletedBlock n) :
    block.inverse.word = inverseWord block.word := by
  cases block with
  | crosscap a negative =>
      cases negative <;> rfl
  | handle a b =>
      rfl
  | boundary carrier hole carrierNegative holeNegative =>
      cases carrierNegative <;>
        cases holeNegative <;> rfl

@[simp]
theorem inverse_inverse {n : ℕ} (block : CompletedBlock n) :
    block.inverse.inverse = block := by
  cases block with
  | crosscap a negative =>
      cases negative <;> rfl
  | handle =>
      rfl
  | boundary carrier hole carrierNegative holeNegative =>
      cases holeNegative <;> rfl

@[simp]
theorem edges_inverse {n : ℕ} (block : CompletedBlock n) :
    block.inverse.edges = block.edges.reverse := by
  cases block <;> rfl

theorem names_inverse_perm {n : ℕ} (block : CompletedBlock n) :
    block.inverse.names.Perm block.names := by
  cases block with
  | crosscap =>
      exact List.Perm.refl _
  | handle a b =>
      exact List.Perm.swap a b []
  | boundary =>
      exact List.Perm.refl _

@[simp]
theorem word_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : CompletedBlock n) :
    (block.mapEquiv e).word =
      block.word.map (SignedDart.mapEquiv e) := by
  cases block with
  | crosscap a negative =>
      cases negative <;> rfl
  | handle =>
      rfl
  | boundary carrier hole carrierNegative holeNegative =>
      cases carrierNegative <;>
        cases holeNegative <;> rfl

@[simp]
theorem edges_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : CompletedBlock n) :
    (block.mapEquiv e).edges = block.edges.map e := by
  cases block <;> rfl

@[simp]
theorem inverse_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : CompletedBlock n) :
    (block.mapEquiv e).inverse =
      block.inverse.mapEquiv e := by
  cases block <;> rfl

@[simp]
theorem mem_map_edgeOfDart_word_iff {n : ℕ}
    (block : CompletedBlock n) (a : Fin n) :
    a ∈ block.word.map edgeOfDart ↔ a ∈ block.edges := by
  cases block with
  | crosscap edge negative =>
      cases negative <;> simp [word, edges]
  | handle first second =>
      simp [word, edges]
      tauto
  | boundary carrier hole carrierNegative holeNegative =>
      cases carrierNegative <;>
        cases holeNegative <;>
          simp [word, edges, boundaryLoopWord]

@[simp]
theorem mem_names_iff_mem_edges {n : ℕ}
    (block : CompletedBlock n) (a : Fin n) :
    a ∈ block.names ↔ a ∈ block.edges := by
  cases block <;> simp [names, edges] ; tauto

/-- Expanding a lowered completed block agrees with word-level cancellation lowering. -/
theorem word_lowerAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (block : CompletedBlock (n + 1))
    (ha : a ∉ block.edges) :
    (block.lowerAvoiding a ha).word =
      Cancellation.lowerTail a block.word := by
  have haWord : a ∉ block.word.map edgeOfDart := by
    simpa only [mem_map_edgeOfDart_word_iff] using ha
  rw [← Cancellation.lowerWordAvoiding_eq_lowerTail
    a block.word haWord]
  cases block with
  | crosscap e negative =>
      cases negative <;>
        simp [lowerAvoiding, word,
          Cancellation.lowerWordAvoiding,
          Cancellation.lowerDart, dart]
  | handle e f =>
      simp [lowerAvoiding, word,
        Cancellation.lowerWordAvoiding,
        Cancellation.lowerDart]
  | boundary carrier hole carrierNegative holeNegative =>
      cases carrierNegative <;>
        cases holeNegative <;>
          simp [lowerAvoiding, word, boundaryLoopWord,
            Cancellation.lowerWordAvoiding,
            Cancellation.lowerDart, dart]

/-- Re-embedding the edge names of a lowered completed block recovers the old edge list. -/
theorem edges_lowerAvoiding_map_restoreEdge {n : ℕ}
    (a : Fin (n + 1))
    (block : CompletedBlock (n + 1))
    (ha : a ∉ block.edges) :
    (block.lowerAvoiding a ha).edges.map
        (Cancellation.restoreEdge a) =
      block.edges := by
  cases block <;>
    simp [lowerAvoiding, edges]

/-- Re-embedding the distinct names of a lowered block recovers its old name spine. -/
theorem names_lowerAvoiding_map_restoreEdge {n : ℕ}
    (a : Fin (n + 1))
    (block : CompletedBlock (n + 1))
    (ha : a ∉ block.edges) :
    (block.lowerAvoiding a ha).names.map
        (Cancellation.restoreEdge a) =
      block.names := by
  cases block <;>
    simp [lowerAvoiding, names]

/-- Concatenate a completed block sequence into its exact signed one-face word. -/
def sequenceWord {n : ℕ} (blocks : List (CompletedBlock n)) :
    List (SignedDart (Fin n)) :=
  (blocks.map word).flatten

@[simp]
theorem sequenceWord_nil {n : ℕ} :
    sequenceWord ([] : List (CompletedBlock n)) = [] :=
  rfl

@[simp]
theorem sequenceWord_cons {n : ℕ}
    (block : CompletedBlock n)
    (blocks : List (CompletedBlock n)) :
    sequenceWord (block :: blocks) =
      block.word ++ sequenceWord blocks := by
  simp [sequenceWord]

@[simp]
theorem sequenceWord_append {n : ℕ}
    (left right : List (CompletedBlock n)) :
    sequenceWord (left ++ right) =
      sequenceWord left ++ sequenceWord right := by
  simp [sequenceWord]

/-- Concatenate the distinct-name spines owned by a completed block sequence. -/
def sequenceNames {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    List (Fin n) :=
  (blocks.map names).flatten

@[simp]
theorem sequenceNames_nil {n : ℕ} :
    sequenceNames ([] : List (CompletedBlock n)) = [] :=
  rfl

@[simp]
theorem sequenceNames_cons {n : ℕ}
    (block : CompletedBlock n)
    (blocks : List (CompletedBlock n)) :
    sequenceNames (block :: blocks) =
      block.names ++ sequenceNames blocks := by
  simp [sequenceNames]

/-- Number of completed crosscap blocks. -/
def crosscapCount {n : ℕ} :
    List (CompletedBlock n) → ℕ
  | [] => 0
  | .crosscap _ _ :: blocks => 1 + crosscapCount blocks
  | _ :: blocks => crosscapCount blocks

/-- Number of completed handle blocks. -/
def handleCount {n : ℕ} :
    List (CompletedBlock n) → ℕ
  | [] => 0
  | .handle _ _ :: blocks => 1 + handleCount blocks
  | _ :: blocks => handleCount blocks

/-- Number of completed boundary-loop blocks. -/
def boundaryCount {n : ℕ} :
    List (CompletedBlock n) → ℕ
  | [] => 0
  | .boundary _ _ _ _ :: blocks =>
      1 + boundaryCount blocks
  | _ :: blocks => boundaryCount blocks

/-- Normal-form parameters selected by a completed block sequence. -/
def normalForm {n : ℕ}
    (blocks : List (CompletedBlock n)) : NormalForm :=
  if crosscapCount blocks = 0 then
    .orientable (handleCount blocks) (boundaryCount blocks)
  else
    .nonOrientable
      (crosscapCount blocks + 2 * handleCount blocks)
      (boundaryCount blocks)

/-- Every completed block belongs to exactly one normal-form block class. -/
theorem count_sum_eq_length {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    boundaryCount blocks + crosscapCount blocks +
        handleCount blocks =
      blocks.length := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp only [boundaryCount, crosscapCount,
          handleCount, List.length_cons] at ih ⊢ <;>
        omega

/-- A nonempty completed block sequence selects an Eval-admissible normal form. -/
theorem normalForm_isEvalAdmissible_of_ne_nil {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hne : blocks ≠ []) :
    (normalForm blocks).IsEvalAdmissible := by
  have hlength : 0 < blocks.length :=
    List.length_pos_iff_ne_nil.mpr hne
  have hsum := count_sum_eq_length blocks
  simp only [normalForm]
  split_ifs with hcrosscap
  · change 1 ≤ handleCount blocks ∨
      1 ≤ boundaryCount blocks
    rw [hcrosscap] at hsum
    omega
  · change
      1 ≤ crosscapCount blocks +
        2 * handleCount blocks
    omega

end CompletedBlock

namespace BoundaryBlockCommute

/-- A completed positive-carrier boundary loop lying inside an opposite residual pair. -/
def sourceWord {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  dart outer outerNegative ::
    (CompletedBlock.boundary carrier hole false
      holeNegative).word ++
    insideTail ++
    dart outer (!outerNegative) ::
    outsideTail

/-- Move the completed loop outside the residual pair, leaving the residual pair around the
strictly shorter protected interval. -/
def targetWord {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  (CompletedBlock.boundary carrier hole false
      holeNegative).word ++
    dart outer outerNegative ::
    insideTail ++
    dart outer (!outerNegative) ::
    outsideTail

/-- The same contextual loop with its carrier displayed negative first. -/
def negativeSourceWord {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  dart outer outerNegative ::
    (CompletedBlock.boundary carrier hole true
      holeNegative).word ++
    insideTail ++
    dart outer (!outerNegative) ::
    outsideTail

/-- Negative-carrier target spelling. -/
def negativeTargetWord {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  (CompletedBlock.boundary carrier hole true
      holeNegative).word ++
    dart outer outerNegative ::
    insideTail ++
    dart outer (!outerNegative) ::
    outsideTail

/-- Positive-carrier boundary-loop commuting is exactly one `LoopGrouping` rewrite between two
cyclic rotations. -/
theorem exists_positiveNormalizationEquivalent {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (sourceWord outer carrier hole outerNegative
          holeNegative insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (targetWord outer carrier hole outerNegative
            holeNegative insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord outer carrier hole outerNegative
            holeNegative insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (targetWord outer carrier hole outerNegative
            holeNegative insideTail outsideTail),
          validTarget⟩ := by
  let loopBody := [dart hole holeNegative]
  let separating :=
    insideTail ++
      [dart outer (!outerNegative)] ++ outsideTail
  let moved := [dart outer outerNegative]
  have hsourceRotated :
      (sourceWord outer carrier hole outerNegative
        holeNegative insideTail outsideTail).IsRotated
        ((LoopGrouping.source carrier
          loopBody separating moved).boundary 0) := by
    simpa [sourceWord, loopBody, separating, moved,
      CompletedBlock.word, boundaryLoopWord, dart,
      LoopGrouping.source, Dyck.oneFace_boundary_zero,
      List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l := [dart outer outerNegative])
        (l' :=
          [SignedDart.pos carrier,
            dart hole holeNegative,
            SignedDart.neg carrier] ++
          insideTail ++
          [dart outer (!outerNegative)] ++
          outsideTail))
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated hsourceRotated
  let validLoopSource :
      (LoopGrouping.source carrier
        loopBody separating moved).IsSurfaceValid :=
    sourceRotation.isSurfaceValid validSource
  have htargetRotated :
      (LoopGrouping.target carrier
        loopBody separating moved).boundary 0 |>.IsRotated
          (targetWord outer carrier hole outerNegative
            holeNegative insideTail outsideTail) := by
    simpa [targetWord, loopBody, separating, moved,
      CompletedBlock.word, boundaryLoopWord, dart,
      List.cons_append, List.append_assoc] using
      (LoopGrouping.target_boundary_isRotated_grouped
        carrier loopBody separating moved)
  let targetRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
  have hperm :
      ((sourceWord outer carrier hole outerNegative
          holeNegative insideTail outsideTail).map
        edgeOfDart).Perm
        ((targetWord outer carrier hole outerNegative
          holeNegative insideTail outsideTail).map
        edgeOfDart) := by
    rw [List.perm_iff_count]
    intro edge
    simp only [sourceWord, targetWord,
      CompletedBlock.word, boundaryLoopWord,
      List.map_cons, List.map_append,
      edgeOfDart_dart, List.count_cons,
      List.count_append]
    omega
  let validTarget :
      (Dyck.oneFace
        (targetWord outer carrier hole outerNegative
          holeNegative insideTail outsideTail)).IsSurfaceValid :=
    Dyck.oneFace_isSurfaceValid_of_edgePerm hperm validSource
  let validLoopTarget :
      (LoopGrouping.target carrier
        loopBody separating moved).IsSurfaceValid :=
    targetRotation.symm.isSurfaceValid validTarget
  have hcarrierBody :
      carrier ∉ loopBody.map edgeOfDart := by
    simp [loopBody, hcarrierHole]
  have hcarrierSeparating :
      carrier ∉ separating.map edgeOfDart := by
    simp [separating, hcarrierInside,
      hcarrierOuter, hcarrierOutside]
  have hcarrierMoved :
      carrier ∉ moved.map edgeOfDart := by
    simp [moved, hcarrierOuter]
  have hgroup :=
    LoopGrouping.normalizationEquivalent carrier
      loopBody separating moved
      hcarrierBody hcarrierSeparating hcarrierMoved
      validLoopSource validLoopTarget
  exact
    ⟨validTarget,
      (NormalizationEquivalent.ofSignedIso sourceRotation).trans
        (hgroup.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩

/-- Reversing only the loop carrier identifies the negative and positive source spellings. -/
def negativeSourceSignedIso {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (negativeSourceWord outer carrier hole
          outerNegative holeNegative insideTail outsideTail))
      (Dyck.oneFace
        (sourceWord outer carrier hole
          outerNegative holeNegative insideTail outsideTail)) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling carrier
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    have houterMap (orientation : Bool) :
        (Dyck.reverseEdgeRelabeling carrier).mapDart
            (dart outer orientation) =
          dart outer orientation := by
      have houterCarrier : outer ≠ carrier :=
        hcarrierOuter.symm
      cases orientation <;>
        simp [dart, Dyck.reverseEdgeRelabeling,
          EdgeRelabeling.mapDart, houterCarrier]
    have hholeMap :
        (Dyck.reverseEdgeRelabeling carrier).mapDart
            (dart hole holeNegative) =
          dart hole holeNegative := by
      have hholeCarrier : hole ≠ carrier :=
        hcarrierHole.symm
      cases holeNegative <;>
        simp [dart, Dyck.reverseEdgeRelabeling,
          EdgeRelabeling.mapDart, hholeCarrier]
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [negativeSourceWord, sourceWord,
      CompletedBlock.word, boundaryLoopWord,
      List.map_cons, List.map_append]
    rw [Dyck.reverseEdgeRelabeling_word carrier
        insideTail hcarrierInside,
      Dyck.reverseEdgeRelabeling_word carrier
        outsideTail hcarrierOutside,
      houterMap outerNegative,
      houterMap (!outerNegative), hholeMap]
    simp only [dart, Bool.not_true, Bool.not_false,
      Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos,
      List.map_nil]
    exact List.IsRotated.refl _

/-- Reversing only the loop carrier identifies the negative and positive target spellings. -/
def negativeTargetSignedIso {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (negativeTargetWord outer carrier hole
          outerNegative holeNegative insideTail outsideTail))
      (Dyck.oneFace
        (targetWord outer carrier hole
          outerNegative holeNegative insideTail outsideTail)) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling carrier
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    have houterMap (orientation : Bool) :
        (Dyck.reverseEdgeRelabeling carrier).mapDart
            (dart outer orientation) =
          dart outer orientation := by
      have houterCarrier : outer ≠ carrier :=
        hcarrierOuter.symm
      cases orientation <;>
        simp [dart, Dyck.reverseEdgeRelabeling,
          EdgeRelabeling.mapDart, houterCarrier]
    have hholeMap :
        (Dyck.reverseEdgeRelabeling carrier).mapDart
            (dart hole holeNegative) =
          dart hole holeNegative := by
      have hholeCarrier : hole ≠ carrier :=
        hcarrierHole.symm
      cases holeNegative <;>
        simp [dart, Dyck.reverseEdgeRelabeling,
          EdgeRelabeling.mapDart, hholeCarrier]
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [negativeTargetWord, targetWord,
      CompletedBlock.word, boundaryLoopWord,
      List.map_cons, List.map_append]
    rw [Dyck.reverseEdgeRelabeling_word carrier
        insideTail hcarrierInside,
      Dyck.reverseEdgeRelabeling_word carrier
        outsideTail hcarrierOutside,
      houterMap outerNegative,
      houterMap (!outerNegative), hholeMap]
    simp only [dart, Bool.not_true, Bool.not_false,
      Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos,
      List.map_nil]
    exact List.IsRotated.refl _

/-- Negative-carrier boundary-loop commuting reduces to the positive theorem by a signed
presentation isomorphism at each endpoint. -/
theorem exists_negativeNormalizationEquivalent {n : ℕ}
    (outer carrier hole : Fin n)
    (outerNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (negativeSourceWord outer carrier hole outerNegative
          holeNegative insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (negativeTargetWord outer carrier hole outerNegative
            holeNegative insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (negativeSourceWord outer carrier hole outerNegative
            holeNegative insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (negativeTargetWord outer carrier hole outerNegative
            holeNegative insideTail outsideTail),
          validTarget⟩ := by
  let sourceIso :=
    negativeSourceSignedIso outer carrier hole
      outerNegative holeNegative insideTail outsideTail
      hcarrierHole hcarrierOuter
      hcarrierInside hcarrierOutside
  let validPositiveSource :
      (Dyck.oneFace
        (sourceWord outer carrier hole outerNegative
          holeNegative insideTail outsideTail)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let positiveWitness :=
    exists_positiveNormalizationEquivalent
      outer carrier hole outerNegative holeNegative
      insideTail outsideTail hcarrierHole hcarrierOuter
      hcarrierInside hcarrierOutside validPositiveSource
  let validPositiveTarget := Classical.choose positiveWitness
  have hpositive := Classical.choose_spec positiveWitness
  let targetIso :=
    negativeTargetSignedIso outer carrier hole
      outerNegative holeNegative insideTail outsideTail
      hcarrierHole hcarrierOuter
      hcarrierInside hcarrierOutside
  let validTarget :
      (Dyck.oneFace
        (negativeTargetWord outer carrier hole outerNegative
          holeNegative insideTail outsideTail)).IsSurfaceValid :=
    targetIso.symm.isSurfaceValid validPositiveTarget
  exact
    ⟨validTarget,
      (NormalizationEquivalent.ofSignedIso sourceIso).trans
        (hpositive.trans
          (NormalizationEquivalent.ofSignedIso targetIso).symm)⟩

end BoundaryBlockCommute

namespace BoundarySingletonClosure

/-- A raw boundary dart already lying between adjacent opposite carrier occurrences, followed by
two contextual tails. -/
def sourceWord {n : ℕ}
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  dart carrier carrierNegative ::
    dart hole holeNegative ::
    dart carrier (!carrierNegative) ::
    insideTail ++ outsideTail

/-- Close the raw boundary dart into a completed loop and move the remaining protected interval
past that loop. -/
def targetWord {n : ℕ}
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  (CompletedBlock.boundary carrier hole
      carrierNegative holeNegative).word ++
    outsideTail ++ insideTail

/-- Positive-carrier contextual boundary closure is exactly one `LoopGrouping` rewrite. -/
theorem exists_positiveNormalizationEquivalent {n : ℕ}
    (carrier hole : Fin n) (holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (sourceWord carrier hole false holeNegative
          insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (targetWord carrier hole false holeNegative
            insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord carrier hole false holeNegative
            insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (targetWord carrier hole false holeNegative
            insideTail outsideTail),
          validTarget⟩ := by
  let loopBody := [dart hole holeNegative]
  have htargetRotated :
      (LoopGrouping.target carrier loopBody
          insideTail outsideTail).boundary 0 |>.IsRotated
        (targetWord carrier hole false holeNegative
          insideTail outsideTail) := by
    simpa [targetWord, loopBody, CompletedBlock.word,
      boundaryLoopWord, List.cons_append,
      List.append_assoc, dart] using
        (LoopGrouping.target_boundary_isRotated_grouped
          carrier loopBody insideTail outsideTail)
  let targetRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
  have hperm :
      ((sourceWord carrier hole false holeNegative
          insideTail outsideTail).map edgeOfDart).Perm
        ((targetWord carrier hole false holeNegative
          insideTail outsideTail).map edgeOfDart) := by
    have hsuffix :
        (insideTail.map edgeOfDart ++
            outsideTail.map edgeOfDart).Perm
          (outsideTail.map edgeOfDart ++
            insideTail.map edgeOfDart) :=
      List.perm_append_comm
    simpa [sourceWord, targetWord,
      CompletedBlock.word, boundaryLoopWord, dart] using
        (List.Perm.cons carrier
          (List.Perm.cons hole
            (List.Perm.cons carrier hsuffix)))
  let validTarget :
      (Dyck.oneFace
        (targetWord carrier hole false holeNegative
          insideTail outsideTail)).IsSurfaceValid :=
    Dyck.oneFace_isSurfaceValid_of_edgePerm hperm validSource
  let validLoopTarget :
      (LoopGrouping.target carrier loopBody
        insideTail outsideTail).IsSurfaceValid :=
    targetRotation.symm.isSurfaceValid validTarget
  have hcarrierBody :
      carrier ∉ loopBody.map edgeOfDart := by
    simp [loopBody, hcarrierHole]
  have hgroup :=
    LoopGrouping.normalizationEquivalent carrier
      loopBody insideTail outsideTail
      hcarrierBody hcarrierInside hcarrierOutside
      (by
        simpa [LoopGrouping.source, loopBody,
          sourceWord, dart, List.cons_append,
          List.append_assoc] using validSource)
      validLoopTarget
  have hsource :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord carrier hole false holeNegative
            insideTail outsideTail),
          validSource⟩
        ⟨LoopGrouping.source carrier loopBody
            insideTail outsideTail,
          by
            simpa [LoopGrouping.source, loopBody,
              sourceWord, dart, List.cons_append,
              List.append_assoc] using validSource⟩ := by
    simpa [LoopGrouping.source, loopBody,
      sourceWord, dart, List.cons_append,
      List.append_assoc] using
        (NormalizationEquivalent.refl
          ⟨Dyck.oneFace
            (sourceWord carrier hole false holeNegative
              insideTail outsideTail),
            validSource⟩)
  exact
    ⟨validTarget,
      hsource.trans
        (hgroup.trans
          (NormalizationEquivalent.ofSignedIso
            targetRotation))⟩

/-- Reversing the carrier identifies negative- and positive-carrier contextual sources. -/
def negativeSourceSignedIso {n : ℕ}
    (carrier hole : Fin n) (holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (sourceWord carrier hole true holeNegative
          insideTail outsideTail))
      (Dyck.oneFace
        (sourceWord carrier hole false holeNegative
          insideTail outsideTail)) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling carrier
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    have hholeMap :
        (Dyck.reverseEdgeRelabeling carrier).mapDart
            (dart hole holeNegative) =
          dart hole holeNegative := by
      have hholeCarrier : hole ≠ carrier :=
        hcarrierHole.symm
      cases holeNegative <;>
        simp [dart, Dyck.reverseEdgeRelabeling,
          EdgeRelabeling.mapDart, hholeCarrier]
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [sourceWord, List.map_cons,
      List.map_append]
    rw [Dyck.reverseEdgeRelabeling_word carrier
        insideTail hcarrierInside,
      Dyck.reverseEdgeRelabeling_word carrier
        outsideTail hcarrierOutside,
      hholeMap]
    simp only [dart, List.cons_append, EdgeRelabeling.mapDart,
      Dyck.reverseEdgeRelabeling, decide_true, ↓reduceIte, Equiv.refl_apply,
      Bool.not_true, Bool.not_false]
    exact List.IsRotated.refl _

/-- Reversing the carrier identifies negative- and positive-carrier contextual targets. -/
def negativeTargetSignedIso {n : ℕ}
    (carrier hole : Fin n) (holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (targetWord carrier hole true holeNegative
          insideTail outsideTail))
      (Dyck.oneFace
        (targetWord carrier hole false holeNegative
          insideTail outsideTail)) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling carrier
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    have hholeMap :
        (Dyck.reverseEdgeRelabeling carrier).mapDart
            (dart hole holeNegative) =
          dart hole holeNegative := by
      have hholeCarrier : hole ≠ carrier :=
        hcarrierHole.symm
      cases holeNegative <;>
        simp [dart, Dyck.reverseEdgeRelabeling,
          EdgeRelabeling.mapDart, hholeCarrier]
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [targetWord, CompletedBlock.word,
      boundaryLoopWord, List.map_cons,
      List.map_append]
    rw [Dyck.reverseEdgeRelabeling_word carrier
        insideTail hcarrierInside,
      Dyck.reverseEdgeRelabeling_word carrier
        outsideTail hcarrierOutside,
      hholeMap]
    simp only [dart, List.cons_append, List.nil_append, EdgeRelabeling.mapDart,
      Dyck.reverseEdgeRelabeling, decide_true, ↓reduceIte, Equiv.refl_apply,
      Bool.not_true, List.map_nil, Bool.not_false]
    exact List.IsRotated.refl _

/-- Negative-carrier contextual boundary closure reduces to the positive theorem through signed
presentation isomorphisms at both endpoints. -/
theorem exists_negativeNormalizationEquivalent {n : ℕ}
    (carrier hole : Fin n) (holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (sourceWord carrier hole true holeNegative
          insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (targetWord carrier hole true holeNegative
            insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord carrier hole true holeNegative
            insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (targetWord carrier hole true holeNegative
            insideTail outsideTail),
          validTarget⟩ := by
  let sourceIso :=
    negativeSourceSignedIso carrier hole holeNegative
      insideTail outsideTail hcarrierHole
      hcarrierInside hcarrierOutside
  let validPositiveSource :
      (Dyck.oneFace
        (sourceWord carrier hole false holeNegative
          insideTail outsideTail)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let positiveWitness :=
    exists_positiveNormalizationEquivalent
      carrier hole holeNegative insideTail outsideTail
      hcarrierHole hcarrierInside hcarrierOutside
      validPositiveSource
  let validPositiveTarget := Classical.choose positiveWitness
  have hpositive := Classical.choose_spec positiveWitness
  let targetIso :=
    negativeTargetSignedIso carrier hole holeNegative
      insideTail outsideTail hcarrierHole
      hcarrierInside hcarrierOutside
  let validTarget :
      (Dyck.oneFace
        (targetWord carrier hole true holeNegative
          insideTail outsideTail)).IsSurfaceValid :=
    targetIso.symm.isSurfaceValid validPositiveTarget
  exact
    ⟨validTarget,
      (NormalizationEquivalent.ofSignedIso sourceIso).trans
        (hpositive.trans
          (NormalizationEquivalent.ofSignedIso targetIso).symm)⟩

end BoundarySingletonClosure

namespace BoundaryAtomRotate

/-- A raw boundary atom followed by a nonempty protected interval inside an opposite pair. -/
def sourceWord {n : ℕ}
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  dart carrier carrierNegative ::
    dart hole holeNegative ::
    insideTail ++
    dart carrier (!carrierNegative) ::
    outsideTail

/-- Move the raw boundary atom to the end of the protected interval, exposing its next atom. -/
def targetWord {n : ℕ}
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  dart carrier carrierNegative ::
    insideTail ++
    dart hole holeNegative ::
    dart carrier (!carrierNegative) ::
    outsideTail

/-- Rotating a raw boundary atom through a protected interval is one signed Dyck rewrite. -/
theorem exists_normalizationEquivalent {n : ℕ}
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierHole : carrier ≠ hole)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (sourceWord carrier hole carrierNegative
          holeNegative insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (targetWord carrier hole carrierNegative
            holeNegative insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord carrier hole carrierNegative
            holeNegative insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (targetWord carrier hole carrierNegative
            holeNegative insideTail outsideTail),
          validTarget⟩ := by
  let raw := [dart hole holeNegative]
  have hcarrierRaw :
      carrier ∉ raw.map edgeOfDart := by
    simp [raw, hcarrierHole]
  cases carrierNegative
  · have hsource :
        Dyck.source carrier raw insideTail outsideTail =
          Dyck.oneFace
            (sourceWord carrier hole false
              holeNegative insideTail outsideTail) := by
      simp [raw, sourceWord, Dyck.source,
        dart, List.cons_append, List.append_assoc]
    have htargetRotated :
        (Dyck.target carrier raw insideTail
            outsideTail).boundary 0 |>.IsRotated
          (targetWord carrier hole false
            holeNegative insideTail outsideTail) := by
      simp only [Dyck.target, Dyck.oneFace_boundary_zero]
      convert
        (List.isRotated_append
          (l :=
            raw ++ [.neg carrier] ++ outsideTail)
          (l' := [.pos carrier] ++ insideTail)) using 1 <;>
        simp [raw, targetWord, dart,
          List.cons_append, List.append_assoc]
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
    let validDyckSource :
        (Dyck.source carrier raw insideTail
          outsideTail).IsSurfaceValid := by
      rw [hsource]
      exact validSource
    let validDyckTarget :=
      Dyck.target_isSurfaceValid carrier raw insideTail
        outsideTail validDyckSource
    let validTarget :
        (Dyck.oneFace
          (targetWord carrier hole false
            holeNegative insideTail outsideTail)).IsSurfaceValid :=
      targetRotation.isSurfaceValid validDyckTarget
    have hdyck :=
      Dyck.normalizationEquivalent carrier raw insideTail
        outsideTail hcarrierRaw hcarrierInside
        hcarrierOutside validDyckSource validDyckTarget
    have hsourceEquivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace
            (sourceWord carrier hole false
              holeNegative insideTail outsideTail),
            validSource⟩
          ⟨Dyck.source carrier raw insideTail outsideTail,
            validDyckSource⟩ := by
      simpa only [hsource] using
        (NormalizationEquivalent.refl
          ⟨Dyck.oneFace
            (sourceWord carrier hole false
              holeNegative insideTail outsideTail),
            validSource⟩)
    exact
      ⟨validTarget,
        hsourceEquivalent.trans
          (hdyck.trans
            (NormalizationEquivalent.ofSignedIso
              targetRotation))⟩
  · have hsource :
        Dyck.negativeSource carrier raw insideTail
            outsideTail =
          Dyck.oneFace
            (sourceWord carrier hole true
              holeNegative insideTail outsideTail) := by
      simp [raw, sourceWord,
        Dyck.negativeSource, dart,
        List.cons_append, List.append_assoc]
    have htargetRotated :
        (Dyck.negativeTarget carrier raw insideTail
            outsideTail).boundary 0 |>.IsRotated
          (targetWord carrier hole true
            holeNegative insideTail outsideTail) := by
      simp only [Dyck.negativeTarget,
        Dyck.oneFace_boundary_zero]
      convert
        (List.isRotated_append
          (l :=
            raw ++ [.pos carrier] ++ outsideTail)
          (l' := [.neg carrier] ++ insideTail)) using 1 <;>
        simp [raw, targetWord, dart,
          List.cons_append, List.append_assoc]
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
    let validDyckSource :
        (Dyck.negativeSource carrier raw insideTail
          outsideTail).IsSurfaceValid := by
      rw [hsource]
      exact validSource
    let validDyckTarget :=
      Dyck.negativeTarget_isSurfaceValid carrier raw
        insideTail outsideTail validDyckSource
    let validTarget :
        (Dyck.oneFace
          (targetWord carrier hole true
            holeNegative insideTail outsideTail)).IsSurfaceValid :=
      targetRotation.isSurfaceValid validDyckTarget
    have hdyck :=
      Dyck.negativeNormalizationEquivalent carrier raw
        insideTail outsideTail hcarrierRaw hcarrierInside
        hcarrierOutside validDyckSource validDyckTarget
    have hsourceEquivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace
            (sourceWord carrier hole true
              holeNegative insideTail outsideTail),
            validSource⟩
          ⟨Dyck.negativeSource carrier raw insideTail
              outsideTail,
            validDyckSource⟩ := by
      simpa only [hsource] using
        (NormalizationEquivalent.refl
          ⟨Dyck.oneFace
            (sourceWord carrier hole true
              holeNegative insideTail outsideTail),
            validSource⟩)
    exact
      ⟨validTarget,
        hsourceEquivalent.trans
          (hdyck.trans
            (NormalizationEquivalent.ofSignedIso
              targetRotation))⟩

end BoundaryAtomRotate

namespace CrosscapBlockCommute

/-- A positive completed crosscap lying at the head of a positive/negative residual pair. -/
def positiveSourceWord {n : ℕ}
    (outer carrier : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  .pos outer :: .pos carrier :: .pos carrier ::
    insideTail ++ .neg outer :: outsideTail

/-- Commute the completed crosscap through the residual pair.  The old residual carrier becomes
the completed crosscap, while the old crosscap carrier becomes the residual pair around the
strictly shorter protected interval. -/
def positiveTargetWord {n : ℕ}
    (outer carrier : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  [.pos outer, .pos outer, .neg carrier] ++
    insideTail ++ .pos carrier :: inverseWord outsideTail

/-- Contextual crosscap source with arbitrary orientations on both distinguished edges. -/
def sourceWord {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  dart outer outerNegative ::
    dart carrier carrierNegative ::
    dart carrier carrierNegative ::
    insideTail ++ dart outer (!outerNegative) ::
      outsideTail

/-- Arbitrarily oriented contextual crosscap target. -/
def targetWord {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  [dart outer outerNegative,
    dart outer outerNegative,
    dart carrier (!carrierNegative)] ++
    insideTail ++ dart carrier carrierNegative ::
      inverseWord outsideTail

/-- Reverse exactly the displayed orientations of the two distinguished edges. -/
def orientationRelabeling {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool) :
    EdgeRelabeling (Fin n) (Fin n) :=
  signedRelabeling (Equiv.refl _) fun edge ↦
    if edge = outer then outerNegative
    else if edge = carrier then carrierNegative
    else false

@[simp]
theorem orientationRelabeling_mapDart_outer {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool) :
    (orientationRelabeling outer carrier
      outerNegative carrierNegative).mapDart
        (dart outer outerNegative) =
      .pos outer := by
  simpa [orientationRelabeling] using
    (signedRelabeling_mapDart_dart_self
      (Equiv.refl (Fin n))
      (fun edge ↦
        if edge = outer then outerNegative
        else if edge = carrier then carrierNegative
        else false)
      outer)

@[simp]
theorem orientationRelabeling_mapDart_outer_opposite {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool) :
    (orientationRelabeling outer carrier
      outerNegative carrierNegative).mapDart
        (dart outer (!outerNegative)) =
      .neg outer := by
  simpa [orientationRelabeling] using
    (signedRelabeling_mapDart_dart_not_self
      (Equiv.refl (Fin n))
      (fun edge ↦
        if edge = outer then outerNegative
        else if edge = carrier then carrierNegative
        else false)
      outer)

@[simp]
theorem orientationRelabeling_mapDart_carrier {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (hcarrierOuter : carrier ≠ outer) :
    (orientationRelabeling outer carrier
      outerNegative carrierNegative).mapDart
        (dart carrier carrierNegative) =
      .pos carrier := by
  simpa [orientationRelabeling, hcarrierOuter] using
    (signedRelabeling_mapDart_dart_self
      (Equiv.refl (Fin n))
      (fun edge ↦
        if edge = outer then outerNegative
        else if edge = carrier then carrierNegative
        else false)
      carrier)

@[simp]
theorem orientationRelabeling_mapDart_carrier_opposite {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (hcarrierOuter : carrier ≠ outer) :
    (orientationRelabeling outer carrier
      outerNegative carrierNegative).mapDart
        (dart carrier (!carrierNegative)) =
      .neg carrier := by
  simpa [orientationRelabeling, hcarrierOuter] using
    (signedRelabeling_mapDart_dart_not_self
      (Equiv.refl (Fin n))
      (fun edge ↦
        if edge = outer then outerNegative
        else if edge = carrier then carrierNegative
        else false)
      carrier)

/-- The two-edge orientation normalization fixes every word avoiding both distinguished names. -/
theorem orientationRelabeling_word {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (word : List (SignedDart (Fin n)))
    (houter : outer ∉ word.map edgeOfDart)
    (hcarrier : carrier ∉ word.map edgeOfDart) :
    word.map
        (orientationRelabeling outer carrier
          outerNegative carrierNegative).mapDart =
      word := by
  induction word with
  | nil =>
      rfl
  | cons head tail ih =>
      have hheadOuter : edgeOfDart head ≠ outer := by
        intro heq
        apply houter
        simp [heq]
      have hheadCarrier : edgeOfDart head ≠ carrier := by
        intro heq
        apply hcarrier
        simp [heq]
      have htailOuter :
          outer ∉ tail.map edgeOfDart := by
        intro hmem
        exact houter (by simp [hmem])
      have htailCarrier :
          carrier ∉ tail.map edgeOfDart := by
        intro hmem
        exact hcarrier (by simp [hmem])
      rw [List.map_cons, ih htailOuter htailCarrier]
      congr 1
      cases head <;>
        simp_all [orientationRelabeling,
          signedRelabeling, EdgeRelabeling.mapDart]

/-- Independent sign normalization identifies the generic and positive source spellings. -/
def sourceSignedIso {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (houterInside :
      outer ∉ insideTail.map edgeOfDart)
    (houterOutside :
      outer ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (sourceWord outer carrier
          outerNegative carrierNegative
          insideTail outsideTail))
      (Dyck.oneFace
        (positiveSourceWord outer carrier
          insideTail outsideTail)) where
  edgeRelabeling :=
    orientationRelabeling outer carrier
      outerNegative carrierNegative
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [sourceWord, positiveSourceWord,
      List.map_cons, List.map_append]
    rw [
      orientationRelabeling_word outer carrier
        outerNegative carrierNegative
        insideTail houterInside hcarrierInside,
      orientationRelabeling_word outer carrier
        outerNegative carrierNegative
        outsideTail houterOutside hcarrierOutside,
      orientationRelabeling_mapDart_outer
        outer carrier outerNegative carrierNegative,
      orientationRelabeling_mapDart_outer_opposite
        outer carrier outerNegative carrierNegative,
      orientationRelabeling_mapDart_carrier
        outer carrier outerNegative carrierNegative
        hcarrierOuter]

/-- Independent sign normalization identifies the generic and positive target spellings. -/
def targetSignedIso {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (houterInside :
      outer ∉ insideTail.map edgeOfDart)
    (houterOutside :
      outer ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (targetWord outer carrier
          outerNegative carrierNegative
          insideTail outsideTail))
      (Dyck.oneFace
        (positiveTargetWord outer carrier
          insideTail outsideTail)) where
  edgeRelabeling :=
    orientationRelabeling outer carrier
      outerNegative carrierNegative
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    have houterInverseOutside :
        outer ∉
          (inverseWord outsideTail).map edgeOfDart := by
      simpa [map_edgeOfDart_inverseWord] using
        houterOutside
    have hcarrierInverseOutside :
        carrier ∉
          (inverseWord outsideTail).map edgeOfDart := by
      simpa [map_edgeOfDart_inverseWord] using
        hcarrierOutside
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [targetWord, positiveTargetWord,
      List.map_cons, List.map_append]
    rw [
      orientationRelabeling_word outer carrier
        outerNegative carrierNegative
        insideTail houterInside hcarrierInside,
      orientationRelabeling_word outer carrier
        outerNegative carrierNegative
        (inverseWord outsideTail)
        houterInverseOutside hcarrierInverseOutside,
      orientationRelabeling_mapDart_outer
        outer carrier outerNegative carrierNegative,
      orientationRelabeling_mapDart_carrier
        outer carrier outerNegative carrierNegative
        hcarrierOuter,
      orientationRelabeling_mapDart_carrier_opposite
        outer carrier outerNegative carrierNegative
        hcarrierOuter]
    simp only [List.cons_append, List.nil_append, List.map_nil]
    exact List.IsRotated.refl _

/-- The positive contextual crosscap commute is an adjacent-crosscap rewrite followed by an
ordinary crosscap grouping, with cyclic rotations between the displayed spellings. -/
theorem exists_positiveNormalizationEquivalent {n : ℕ}
    (outer carrier : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (houterInside :
      outer ∉ insideTail.map edgeOfDart)
    (houterOutside :
      outer ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (positiveSourceWord outer carrier
          insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (positiveTargetWord outer carrier
            insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (positiveSourceWord outer carrier
            insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (positiveTargetWord outer carrier
            insideTail outsideTail),
          validTarget⟩ := by
  let adjacentX :=
    insideTail ++ [.neg outer] ++ outsideTail
  let adjacentY : List (SignedDart (Fin n)) :=
    [.pos outer]
  have hsourceRotated :
      (positiveSourceWord outer carrier
        insideTail outsideTail).IsRotated
        ((Crosscap.adjacentSource carrier
          adjacentX adjacentY).boundary 0) := by
    simpa [positiveSourceWord, adjacentX, adjacentY,
      Crosscap.adjacentSource, Dyck.oneFace_boundary_zero,
      List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l := [SignedDart.pos outer])
        (l' :=
          [SignedDart.pos carrier,
            SignedDart.pos carrier] ++
          insideTail ++ [SignedDart.neg outer] ++
          outsideTail))
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated hsourceRotated
  let validAdjacentSource :
      (Crosscap.adjacentSource carrier
        adjacentX adjacentY).IsSurfaceValid :=
    sourceRotation.isSurfaceValid validSource
  have hcarrierAdjacentX :
      carrier ∉ adjacentX.map edgeOfDart := by
    simp [adjacentX, hcarrierInside,
      hcarrierOuter, hcarrierOutside]
  have hcarrierAdjacentY :
      carrier ∉ adjacentY.map edgeOfDart := by
    simp [adjacentY, hcarrierOuter]
  let validAdjacentTarget :=
    Crosscap.adjacentTarget_isSurfaceValid carrier
      adjacentX adjacentY validAdjacentSource
  have hadjacent :=
    Crosscap.adjacentNormalizationEquivalent carrier
      adjacentX adjacentY
      hcarrierAdjacentX hcarrierAdjacentY
      validAdjacentSource validAdjacentTarget
  let groupingX :=
    SignedDart.pos carrier ::
      inverseWord outsideTail
  let groupingY :=
    inverseWord insideTail ++
      [SignedDart.pos carrier]
  have hadjacentTargetRotated :
      (Crosscap.adjacentTarget carrier
        adjacentX adjacentY).boundary 0 |>.IsRotated
        ((Crosscap.source outer
          groupingX groupingY).boundary 0) := by
    simpa [adjacentX, adjacentY, groupingX, groupingY,
      Crosscap.adjacentTarget, Crosscap.source,
      Dyck.oneFace_boundary_zero, inverseWord,
      SignedDart.flip, Function.comp_def,
      List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l := [SignedDart.pos carrier])
        (l' :=
          [SignedDart.pos outer,
            SignedDart.pos carrier] ++
          inverseWord outsideTail ++
          [SignedDart.pos outer] ++
          inverseWord insideTail))
  let groupingRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      hadjacentTargetRotated
  let validGroupingSource :
      (Crosscap.source outer
        groupingX groupingY).IsSurfaceValid :=
    groupingRotation.isSurfaceValid validAdjacentTarget
  have houterGroupingX :
      outer ∉ groupingX.map edgeOfDart := by
    simp [groupingX, hcarrierOuter.symm,
      map_edgeOfDart_inverseWord, houterOutside]
  have houterGroupingY :
      outer ∉ groupingY.map edgeOfDart := by
    simp [groupingY, map_edgeOfDart_inverseWord,
      houterInside, hcarrierOuter.symm]
  let validGroupingTarget :=
    Crosscap.target_isSurfaceValid outer
      groupingX groupingY validGroupingSource
  have hgrouping :=
    Crosscap.normalizationEquivalent outer
      groupingX groupingY
      houterGroupingX houterGroupingY
      validGroupingSource validGroupingTarget
  have hinverseGroupingY :
      inverseWord groupingY =
        SignedDart.neg carrier :: insideTail := by
    simp [groupingY, inverseWord_append]
    rfl
  have htargetRotated :
      (Crosscap.target outer
        groupingX groupingY).boundary 0 |>.IsRotated
        (positiveTargetWord outer carrier
          insideTail outsideTail) := by
    simpa [positiveTargetWord, groupingX, groupingY,
      Crosscap.target, Dyck.oneFace_boundary_zero,
      hinverseGroupingY, List.cons_append,
      List.append_assoc] using
      (List.isRotated_append
        (l :=
          SignedDart.pos carrier ::
            inverseWord outsideTail)
        (l' :=
          [SignedDart.pos outer,
            SignedDart.pos outer,
            SignedDart.neg carrier] ++
          insideTail))
  let targetRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
  let validTarget :
      (Dyck.oneFace
        (positiveTargetWord outer carrier
          insideTail outsideTail)).IsSurfaceValid :=
    targetRotation.isSurfaceValid validGroupingTarget
  exact
    ⟨validTarget,
      (NormalizationEquivalent.ofSignedIso sourceRotation).trans
        (hadjacent.trans
          ((NormalizationEquivalent.ofSignedIso
              groupingRotation).trans
            (hgrouping.trans
              (NormalizationEquivalent.ofSignedIso
                targetRotation))))⟩

/-- Contextual crosscap commuting supports arbitrary orientations on both distinguished edges. -/
theorem exists_normalizationEquivalent {n : ℕ}
    (outer carrier : Fin n)
    (outerNegative carrierNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hcarrierOuter : carrier ≠ outer)
    (hcarrierInside :
      carrier ∉ insideTail.map edgeOfDart)
    (hcarrierOutside :
      carrier ∉ outsideTail.map edgeOfDart)
    (houterInside :
      outer ∉ insideTail.map edgeOfDart)
    (houterOutside :
      outer ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (sourceWord outer carrier
          outerNegative carrierNegative
          insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (targetWord outer carrier
            outerNegative carrierNegative
            insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord outer carrier
            outerNegative carrierNegative
            insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (targetWord outer carrier
            outerNegative carrierNegative
            insideTail outsideTail),
          validTarget⟩ := by
  let sourceIso :=
    sourceSignedIso outer carrier
      outerNegative carrierNegative
      insideTail outsideTail hcarrierOuter
      hcarrierInside hcarrierOutside
      houterInside houterOutside
  let validPositiveSource :
      (Dyck.oneFace
        (positiveSourceWord outer carrier
          insideTail outsideTail)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let positiveWitness :=
    exists_positiveNormalizationEquivalent
      outer carrier insideTail outsideTail
      hcarrierOuter hcarrierInside hcarrierOutside
      houterInside houterOutside validPositiveSource
  let validPositiveTarget :=
    Classical.choose positiveWitness
  have hpositive :=
    Classical.choose_spec positiveWitness
  let targetIso :=
    targetSignedIso outer carrier
      outerNegative carrierNegative
      insideTail outsideTail hcarrierOuter
      hcarrierInside hcarrierOutside
      houterInside houterOutside
  let validTarget :
      (Dyck.oneFace
        (targetWord outer carrier
          outerNegative carrierNegative
          insideTail outsideTail)).IsSurfaceValid :=
    targetIso.symm.isSurfaceValid validPositiveTarget
  exact
    ⟨validTarget,
      (NormalizationEquivalent.ofSignedIso sourceIso).trans
        (hpositive.trans
          (NormalizationEquivalent.ofSignedIso
            targetIso).symm)⟩

end CrosscapBlockCommute

namespace HandleBlockCommute

/-- A completed handle at the head of a positive/negative residual pair. -/
def positiveSourceWord {n : ℕ}
    (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  [.pos outer, .pos first, .pos second,
    .neg first, .neg second] ++
    insideTail ++ .neg outer :: outsideTail

/-- The same completed handle commuted outside the residual pair. -/
def positiveTargetWord {n : ℕ}
    (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  [.pos first, .pos second, .neg first,
    .neg second, .pos outer] ++
    insideTail ++ .neg outer :: outsideTail

/-- The contextual handle source with its residual carrier displayed negative first. -/
def negativeSourceWord {n : ℕ}
    (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  [.neg outer, .pos first, .pos second,
    .neg first, .neg second] ++
    insideTail ++ .pos outer :: outsideTail

/-- Negative-residual-carrier target spelling. -/
def negativeTargetWord {n : ℕ}
    (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  [.pos first, .pos second, .neg first,
    .neg second, .neg outer] ++
    insideTail ++ .pos outer :: outsideTail

/-- Contextual handle source with arbitrary residual-carrier orientation. -/
def sourceWord {n : ℕ}
    (outer first second : Fin n)
    (outerNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  if outerNegative then
    negativeSourceWord outer first second
      insideTail outsideTail
  else
    positiveSourceWord outer first second
      insideTail outsideTail

@[simp]
private theorem sourceWord_false {n : ℕ} (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    sourceWord outer first second false insideTail outsideTail =
      positiveSourceWord outer first second insideTail outsideTail := by
  simp [sourceWord]

/-- Contextual handle target with arbitrary residual-carrier orientation. -/
def targetWord {n : ℕ}
    (outer first second : Fin n)
    (outerNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    List (SignedDart (Fin n)) :=
  if outerNegative then
    negativeTargetWord outer first second
      insideTail outsideTail
  else
    positiveTargetWord outer first second
      insideTail outsideTail

@[simp]
private theorem targetWord_false {n : ℕ} (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n))) :
    targetWord outer first second false insideTail outsideTail =
      positiveTargetWord outer first second insideTail outsideTail := by
  simp [targetWord]

/-- Reversing only the residual carrier identifies negative and positive handle sources. -/
def negativeSourceSignedIso {n : ℕ}
    (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hfirstOuter : first ≠ outer)
    (hsecondOuter : second ≠ outer)
    (houterInside :
      outer ∉ insideTail.map edgeOfDart)
    (houterOutside :
      outer ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (negativeSourceWord outer first second
          insideTail outsideTail))
      (Dyck.oneFace
        (positiveSourceWord outer first second
          insideTail outsideTail)) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling outer
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    have hfirstPos :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.pos first) =
          .pos first := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer first hfirstOuter false)
    have hfirstNeg :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.neg first) =
          .neg first := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer first hfirstOuter true)
    have hsecondPos :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.pos second) =
          .pos second := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer second hsecondOuter false)
    have hsecondNeg :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.neg second) =
          .neg second := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer second hsecondOuter true)
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [negativeSourceWord,
      positiveSourceWord, List.map_append,
      List.map_cons]
    rw [Dyck.reverseEdgeRelabeling_word outer
        insideTail houterInside,
      Dyck.reverseEdgeRelabeling_word outer
        outsideTail houterOutside,
      hfirstPos, hsecondPos,
      hfirstNeg, hsecondNeg]
    simp only [Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos, List.map_nil]
    exact List.IsRotated.refl _

/-- Reversing only the residual carrier identifies negative and positive handle targets. -/
def negativeTargetSignedIso {n : ℕ}
    (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hfirstOuter : first ≠ outer)
    (hsecondOuter : second ≠ outer)
    (houterInside :
      outer ∉ insideTail.map edgeOfDart)
    (houterOutside :
      outer ∉ outsideTail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (negativeTargetWord outer first second
          insideTail outsideTail))
      (Dyck.oneFace
        (positiveTargetWord outer first second
          insideTail outsideTail)) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling outer
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    have hfirstPos :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.pos first) =
          .pos first := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer first hfirstOuter false)
    have hfirstNeg :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.neg first) =
          .neg first := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer first hfirstOuter true)
    have hsecondPos :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.pos second) =
          .pos second := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer second hsecondOuter false)
    have hsecondNeg :
        (Dyck.reverseEdgeRelabeling outer).mapDart
            (.neg second) =
          .neg second := by
      simpa using
        (Dyck.reverseEdgeRelabeling_of_ne
          outer second hsecondOuter true)
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [negativeTargetWord,
      positiveTargetWord, List.map_append,
      List.map_cons]
    rw [Dyck.reverseEdgeRelabeling_word outer
        insideTail houterInside,
      Dyck.reverseEdgeRelabeling_word outer
        outsideTail houterOutside,
      hfirstPos, hsecondPos,
      hfirstNeg, hsecondNeg]
    simp only [Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos, List.map_nil]
    exact List.IsRotated.refl _

private theorem exists_positiveTarget_of_thirdTarget {n : ℕ}
    (outer first second : Fin n) (insideTail outsideTail : List (SignedDart (Fin n)))
    (hfirstSecond : first ≠ second) (hsecondOuter : second ≠ outer)
    (hsecondInside : second ∉ insideTail.map edgeOfDart)
    (hsecondOutside : second ∉ outsideTail.map edgeOfDart)
    (validSource : (Dyck.target first [.pos second] [.pos outer]
      (SignedDart.neg second :: insideTail ++ SignedDart.neg outer :: outsideTail)).IsSurfaceValid) :
    ∃ validTarget : (Dyck.oneFace
        (positiveTargetWord outer first second insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.target first [.pos second] [.pos outer]
          (SignedDart.neg second :: insideTail ++ SignedDart.neg outer :: outsideTail),
          validSource⟩
        ⟨Dyck.oneFace (positiveTargetWord outer first second insideTail outsideTail),
          validTarget⟩ := by
  let fourthU :=
    insideTail ++ SignedDart.neg outer :: outsideTail ++ [SignedDart.pos first]
  let fourthV : List (SignedDart (Fin n)) := [.pos outer]
  let fourthX : List (SignedDart (Fin n)) := [.neg first]
  have hthirdTargetRotated :
      (Dyck.target first [.pos second] [.pos outer]
        (SignedDart.neg second :: insideTail ++ SignedDart.neg outer :: outsideTail)
        ).boundary 0 |>.IsRotated
        ((Dyck.negativeSource second fourthU fourthV fourthX).boundary 0) := by
    simpa [fourthU, fourthV, fourthX, Dyck.target, Dyck.negativeSource,
      Dyck.oneFace_boundary_zero, List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l := [SignedDart.pos second, SignedDart.neg first])
        (l' := [SignedDart.neg second] ++ insideTail ++ [SignedDart.neg outer] ++
          outsideTail ++ [SignedDart.pos first, SignedDart.pos outer]))
  let thirdTargetRotation := Dyck.oneFaceSignedIsoOfIsRotated hthirdTargetRotated
  let validFourthSource :
      (Dyck.negativeSource second fourthU fourthV fourthX).IsSurfaceValid :=
    thirdTargetRotation.isSurfaceValid validSource
  have hfourthU : second ∉ fourthU.map edgeOfDart := by
    simp [fourthU, hsecondInside, hsecondOuter, hsecondOutside, hfirstSecond.symm]
  have hfourthV : second ∉ fourthV.map edgeOfDart := by
    simp [fourthV, hsecondOuter]
  have hfourthX : second ∉ fourthX.map edgeOfDart := by
    simp [fourthX, hfirstSecond.symm]
  let validFourthTarget :=
    Dyck.negativeTarget_isSurfaceValid second fourthU fourthV fourthX validFourthSource
  have hfourth := Dyck.negativeNormalizationEquivalent second fourthU fourthV fourthX
    hfourthU hfourthV hfourthX validFourthSource validFourthTarget
  have htargetRotated :
      (Dyck.negativeTarget second fourthU fourthV fourthX).boundary 0 |>.IsRotated
        (positiveTargetWord outer first second insideTail outsideTail) := by
    simpa [fourthU, fourthV, fourthX, positiveTargetWord, Dyck.negativeTarget,
      Dyck.oneFace_boundary_zero, List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l := insideTail ++ SignedDart.neg outer :: outsideTail)
        (l' := [SignedDart.pos first, SignedDart.pos second, SignedDart.neg first,
          SignedDart.neg second, SignedDart.pos outer]))
  let targetRotation := Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
  let validTarget : (Dyck.oneFace
      (positiveTargetWord outer first second insideTail outsideTail)).IsSurfaceValid :=
    targetRotation.isSurfaceValid validFourthTarget
  exact ⟨validTarget, (NormalizationEquivalent.ofSignedIso thirdTargetRotation).trans
    (hfourth.trans (NormalizationEquivalent.ofSignedIso targetRotation))⟩

/-- Commuting a completed handle through a residual pair is a four-Dyck chain. -/
theorem exists_positiveNormalizationEquivalent {n : ℕ}
    (outer first second : Fin n)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hfirstSecond : first ≠ second)
    (hfirstOuter : first ≠ outer)
    (hsecondOuter : second ≠ outer)
    (hfirstInside :
      first ∉ insideTail.map edgeOfDart)
    (hfirstOutside :
      first ∉ outsideTail.map edgeOfDart)
    (hsecondInside :
      second ∉ insideTail.map edgeOfDart)
    (hsecondOutside :
      second ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (positiveSourceWord outer first second
          insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (positiveTargetWord outer first second
            insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (positiveSourceWord outer first second
            insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (positiveTargetWord outer first second
            insideTail outsideTail),
          validTarget⟩ := by
  let firstU :=
    SignedDart.neg second ::
      insideTail ++
      SignedDart.neg outer :: outsideTail
  let firstV : List (SignedDart (Fin n)) :=
    [.pos outer]
  let firstX : List (SignedDart (Fin n)) :=
    [.pos second]
  have hsourceRotated :
      (positiveSourceWord outer first second
        insideTail outsideTail).IsRotated
        ((Dyck.negativeSource first
          firstU firstV firstX).boundary 0) := by
    simpa [positiveSourceWord, firstU, firstV, firstX,
      Dyck.negativeSource, Dyck.oneFace_boundary_zero,
      List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l :=
          [SignedDart.pos outer,
            SignedDart.pos first,
            SignedDart.pos second])
        (l' :=
          [SignedDart.neg first,
            SignedDart.neg second] ++
          insideTail ++
          SignedDart.neg outer :: outsideTail))
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated hsourceRotated
  let validFirstSource :
      (Dyck.negativeSource first
        firstU firstV firstX).IsSurfaceValid :=
    sourceRotation.isSurfaceValid validSource
  have hfirstU :
      first ∉ firstU.map edgeOfDart := by
    simp [firstU, hfirstSecond,
      hfirstInside, hfirstOuter, hfirstOutside]
  have hfirstV :
      first ∉ firstV.map edgeOfDart := by
    simp [firstV, hfirstOuter]
  have hfirstX :
      first ∉ firstX.map edgeOfDart := by
    simp [firstX, hfirstSecond]
  let validFirstTarget :=
    Dyck.negativeTarget_isSurfaceValid first
      firstU firstV firstX validFirstSource
  have hfirst :=
    Dyck.negativeNormalizationEquivalent first
      firstU firstV firstX
      hfirstU hfirstV hfirstX
      validFirstSource validFirstTarget
  let secondU : List (SignedDart (Fin n)) :=
    [.neg first]
  let secondV : List (SignedDart (Fin n)) :=
    [.pos outer]
  let secondX :=
    insideTail ++
      SignedDart.neg outer ::
      outsideTail ++ [SignedDart.pos first]
  have hfirstTargetRotated :
      (Dyck.negativeTarget first
        firstU firstV firstX).boundary 0 |>.IsRotated
        ((Dyck.source second
          secondU secondV secondX).boundary 0) := by
    simpa [firstU, firstV, firstX,
      secondU, secondV, secondX,
      Dyck.negativeTarget, Dyck.source,
      Dyck.oneFace_boundary_zero,
      List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l :=
          firstU ++ [SignedDart.pos first])
        (l' :=
          [SignedDart.pos second,
            SignedDart.neg first,
            SignedDart.pos outer]))
  let firstTargetRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      hfirstTargetRotated
  let validSecondSource :
      (Dyck.source second
        secondU secondV secondX).IsSurfaceValid :=
    firstTargetRotation.isSurfaceValid validFirstTarget
  have hsecondU :
      second ∉ secondU.map edgeOfDart := by
    simp [secondU, hfirstSecond.symm]
  have hsecondV :
      second ∉ secondV.map edgeOfDart := by
    simp [secondV, hsecondOuter]
  have hsecondX :
      second ∉ secondX.map edgeOfDart := by
    simp [secondX, hsecondInside, hsecondOuter,
      hsecondOutside, hfirstSecond.symm]
  let validSecondTarget :=
    Dyck.target_isSurfaceValid second
      secondU secondV secondX validSecondSource
  have hsecond :=
    Dyck.normalizationEquivalent second
      secondU secondV secondX
      hsecondU hsecondV hsecondX
      validSecondSource validSecondTarget
  let thirdU : List (SignedDart (Fin n)) :=
    [.pos second]
  let thirdV : List (SignedDart (Fin n)) :=
    [.pos outer]
  let thirdX :=
    SignedDart.neg second ::
      insideTail ++
      SignedDart.neg outer :: outsideTail
  have hsecondTargetRotated :
      (Dyck.target second
        secondU secondV secondX).boundary 0 |>.IsRotated
        ((Dyck.source first
          thirdU thirdV thirdX).boundary 0) := by
    simpa [secondU, secondV, secondX,
      thirdU, thirdV, thirdX,
      Dyck.target, Dyck.source,
      Dyck.oneFace_boundary_zero,
      List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l :=
          [SignedDart.neg first,
            SignedDart.neg second] ++
          insideTail ++
          SignedDart.neg outer :: outsideTail)
        (l' :=
          [SignedDart.pos first,
            SignedDart.pos second,
            SignedDart.pos outer]))
  let secondTargetRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      hsecondTargetRotated
  let validThirdSource :
      (Dyck.source first
        thirdU thirdV thirdX).IsSurfaceValid :=
    secondTargetRotation.isSurfaceValid validSecondTarget
  have hthirdU :
      first ∉ thirdU.map edgeOfDart := by
    simp [thirdU, hfirstSecond]
  have hthirdV :
      first ∉ thirdV.map edgeOfDart := by
    simp [thirdV, hfirstOuter]
  have hthirdX :
      first ∉ thirdX.map edgeOfDart := by
    simp [thirdX, hfirstSecond, hfirstInside,
      hfirstOuter, hfirstOutside]
  let validThirdTarget :=
    Dyck.target_isSurfaceValid first
      thirdU thirdV thirdX validThirdSource
  have hthird :=
    Dyck.normalizationEquivalent first
      thirdU thirdV thirdX
      hthirdU hthirdV hthirdX
      validThirdSource validThirdTarget
  let finalWitness := exists_positiveTarget_of_thirdTarget outer first second
    insideTail outsideTail hfirstSecond hsecondOuter hsecondInside hsecondOutside validThirdTarget
  let validTarget := Classical.choose finalWitness
  have hfinal := Classical.choose_spec finalWitness
  exact ⟨validTarget, (NormalizationEquivalent.ofSignedIso sourceRotation).trans
    (hfirst.trans ((NormalizationEquivalent.ofSignedIso firstTargetRotation).trans
      (hsecond.trans ((NormalizationEquivalent.ofSignedIso secondTargetRotation).trans
        (hthird.trans hfinal)))))⟩

/-- Contextual handle commuting supports either orientation of the residual carrier. -/
theorem exists_normalizationEquivalent {n : ℕ}
    (outer first second : Fin n)
    (outerNegative : Bool)
    (insideTail outsideTail : List (SignedDart (Fin n)))
    (hfirstSecond : first ≠ second)
    (hfirstOuter : first ≠ outer)
    (hsecondOuter : second ≠ outer)
    (hfirstInside :
      first ∉ insideTail.map edgeOfDart)
    (hfirstOutside :
      first ∉ outsideTail.map edgeOfDart)
    (hsecondInside :
      second ∉ insideTail.map edgeOfDart)
    (hsecondOutside :
      second ∉ outsideTail.map edgeOfDart)
    (houterInside :
      outer ∉ insideTail.map edgeOfDart)
    (houterOutside :
      outer ∉ outsideTail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (sourceWord outer first second
          outerNegative insideTail outsideTail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (targetWord outer first second
            outerNegative insideTail outsideTail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord outer first second
            outerNegative insideTail outsideTail),
          validSource⟩
        ⟨Dyck.oneFace
          (targetWord outer first second
            outerNegative insideTail outsideTail),
          validTarget⟩ := by
  cases outerNegative with
  | false =>
    simpa [sourceWord, targetWord] using
      (exists_positiveNormalizationEquivalent
        outer first second insideTail outsideTail
        hfirstSecond hfirstOuter hsecondOuter
        hfirstInside hfirstOutside
        hsecondInside hsecondOutside validSource)
  | true =>
    let sourceIso :=
      negativeSourceSignedIso outer first second
        insideTail outsideTail
        hfirstOuter hsecondOuter
        houterInside houterOutside
    let validPositiveSource :
        (Dyck.oneFace
          (positiveSourceWord outer first second
            insideTail outsideTail)).IsSurfaceValid :=
      sourceIso.isSurfaceValid (by
        simpa [sourceWord] using validSource)
    let positiveWitness :=
      exists_positiveNormalizationEquivalent
        outer first second insideTail outsideTail
        hfirstSecond hfirstOuter hsecondOuter
        hfirstInside hfirstOutside
        hsecondInside hsecondOutside
        validPositiveSource
    let validPositiveTarget :=
      Classical.choose positiveWitness
    have hpositive :=
      Classical.choose_spec positiveWitness
    let targetIso :=
      negativeTargetSignedIso outer first second
        insideTail outsideTail
        hfirstOuter hsecondOuter
        houterInside houterOutside
    let validTarget :
        (Dyck.oneFace
          (negativeTargetWord outer first second
            insideTail outsideTail)).IsSurfaceValid :=
      targetIso.symm.isSurfaceValid validPositiveTarget
    have result :
        ∃ validNegativeTarget :
            (Dyck.oneFace
              (negativeTargetWord outer first second
                insideTail outsideTail)).IsSurfaceValid,
          NormalizationEquivalent
            ⟨Dyck.oneFace
              (negativeSourceWord outer first second
                insideTail outsideTail),
              (by
                simpa [sourceWord] using validSource)⟩
            ⟨Dyck.oneFace
              (negativeTargetWord outer first second
                insideTail outsideTail),
              validNegativeTarget⟩ :=
      ⟨validTarget,
        (NormalizationEquivalent.ofSignedIso sourceIso).trans
          (hpositive.trans
            (NormalizationEquivalent.ofSignedIso
              targetIso).symm)⟩
    simpa [sourceWord, targetWord] using result

end HandleBlockCommute

namespace BoundaryPairContraction

/-- Two consecutive extracted boundary darts with arbitrary independent orientations. -/
def sourceWord {n : ℕ}
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (tail : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin (n + 1))) :=
  [dart first firstNegative,
    dart second secondNegative] ++ tail

/-- Contract the second boundary edge and retain one positively normalized boundary dart. -/
def targetWord {n : ℕ}
    (first second : Fin (n + 1))
    (hfirstSecond : first ≠ second)
    (tail : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin n)) :=
  .pos (Cancellation.lowerEdge second first
      hfirstSecond) ::
    Cancellation.lowerTail second tail

/-- P1 expansion is just edge-name retention on a word avoiding the subdivided edge. -/
theorem expandWord_avoiding {n : ℕ}
    (edge : Fin n)
    (word : List (SignedDart (Fin n)))
    (hedge : edge ∉ word.map edgeOfDart) :
    P1.expandWord edge word =
      P2.retainWord word := by
  induction word with
  | nil =>
      rfl
  | cons head tail ih =>
      have hhead : edgeOfDart head ≠ edge := by
        intro heq
        apply hedge
        simp [heq]
      have htail :
          edge ∉ tail.map edgeOfDart := by
        intro hmem
        exact hedge (by simp [hmem])
      rw [P1.expandWord_cons, ih htail]
      cases head with
      | pos old =>
          have hold : old ≠ edge := by
            simpa using hhead
          rw [P1.expandDart_pos_of_ne hold]
          rfl
      | neg old =>
          have hold : old ≠ edge := by
            simpa using hhead
          rw [P1.expandDart_neg_of_ne hold]
          rfl

/-- Independent sign normalization identifies the generic and positive adjacent-boundary
spellings. -/
def sourceSignSignedIso {n : ℕ}
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (tail : List (SignedDart (Fin (n + 1))))
    (hfirstSecond : first ≠ second)
    (hfirstTail :
      first ∉ tail.map edgeOfDart)
    (hsecondTail :
      second ∉ tail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (sourceWord first second
          firstNegative secondNegative tail))
      (Dyck.oneFace
        (sourceWord first second false false tail)) where
  edgeRelabeling :=
    CrosscapBlockCommute.orientationRelabeling
      first second firstNegative secondNegative
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [sourceWord, List.map_append,
      List.map_cons]
    rw [
      CrosscapBlockCommute.orientationRelabeling_word
        first second firstNegative secondNegative
        tail hfirstTail hsecondTail,
      CrosscapBlockCommute.orientationRelabeling_mapDart_outer
        first second firstNegative secondNegative,
      CrosscapBlockCommute.orientationRelabeling_mapDart_carrier
        first second firstNegative secondNegative
        hfirstSecond.symm]
    exact List.IsRotated.refl _

/-- The positive adjacent-boundary spelling is exactly a P1 expansion after moving the second
edge to the fresh-last name. -/
def positiveSourceSignedIso {n : ℕ}
    (first second : Fin (n + 1))
    (tail : List (SignedDart (Fin (n + 1))))
    (hfirstSecond : first ≠ second)
    (hfirstTail :
      first ∉ tail.map edgeOfDart)
    (hsecondTail :
      second ∉ tail.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (sourceWord first second false false tail))
      (P1.expand
        (Dyck.oneFace
          (targetWord first second
            hfirstSecond tail))
        (Cancellation.lowerEdge second first
          hfirstSecond)) where
  edgeRelabeling :=
    EdgeRelabeling.ofEquiv
      (Cancellation.moveToLast second)
  faceEquiv :=
    P1.faceEquiv
      (Dyck.oneFace
        (targetWord first second
          hfirstSecond tail))
      (Cancellation.lowerEdge second first
        hfirstSecond)
  boundary_rotated := by
    intro face
    let loweredFirst :=
      Cancellation.lowerEdge second first
        hfirstSecond
    have hloweredFirstTail :
        loweredFirst ∉
          (Cancellation.lowerTail second tail).map
            edgeOfDart := by
      intro hmem
      have hrestored :
          first ∈ tail.map edgeOfDart := by
        rw [← Cancellation.restoreEdges_lowerTail
          second tail hsecondTail]
        exact List.mem_map.mpr
          ⟨loweredFirst, hmem,
            Cancellation.restoreEdge_lowerEdge
              second first hfirstSecond⟩
      exact hfirstTail hrestored
    have hfirstMove :
        Cancellation.moveToLast second first =
          loweredFirst.castSucc :=
      (Cancellation.castSucc_lowerEdge
        second first hfirstSecond).symm
    have hsecondMove :
        Cancellation.moveToLast second second =
          P1.freshEdge n := by
      simp [Cancellation.moveToLast,
        P1.freshEdge]
    rw [Dyck.oneFace_boundary,
      P1.expand_boundary, Dyck.oneFace_boundary]
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    simp only [sourceWord, targetWord,
      List.map_append, List.map_cons,
      List.map_nil, P1.expandWord_cons,
      P1.expandDart_pos_self]
    rw [expandWord_avoiding loweredFirst
        (Cancellation.lowerTail second tail)
        hloweredFirstTail,
      Cancellation.retainWord_lowerTail
        second tail hsecondTail]
    change
      ([SignedDart.pos
          (Cancellation.moveToLast second first),
        SignedDart.pos
          (Cancellation.moveToLast second second)] ++
        Cancellation.renamedTail second tail).IsRotated
      ([SignedDart.pos (P1.firstSubedge loweredFirst),
        SignedDart.pos (P1.freshEdge n)] ++
        Cancellation.renamedTail second tail)
    rw [hfirstMove, hsecondMove]
    exact List.IsRotated.refl _

/-- Contracting two adjacent once-used boundary darts is a signed isomorphism followed by one
inverse P1 move. -/
theorem exists_normalizationEquivalent {n : ℕ}
    (first second : Fin (n + 1))
    (firstNegative secondNegative : Bool)
    (tail : List (SignedDart (Fin (n + 1))))
    (hfirstSecond : first ≠ second)
    (hfirstTail :
      first ∉ tail.map edgeOfDart)
    (hsecondTail :
      second ∉ tail.map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (sourceWord first second
          firstNegative secondNegative
          tail)).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (targetWord first second
            hfirstSecond tail)).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord first second
            firstNegative secondNegative tail),
          validSource⟩
        ⟨Dyck.oneFace
          (targetWord first second
            hfirstSecond tail),
          validTarget⟩ := by
  let signIso :=
    sourceSignSignedIso first second
      firstNegative secondNegative tail
      hfirstSecond hfirstTail hsecondTail
  let validPositiveSource :
      (Dyck.oneFace
        (sourceWord first second false false
          tail)).IsSurfaceValid :=
    signIso.isSurfaceValid validSource
  let expansionIso :=
    positiveSourceSignedIso first second tail
      hfirstSecond hfirstTail hsecondTail
  let validExpansion :
      (P1.expand
        (Dyck.oneFace
          (targetWord first second
            hfirstSecond tail))
        (Cancellation.lowerEdge second first
          hfirstSecond)).IsSurfaceValid :=
    expansionIso.isSurfaceValid validPositiveSource
  let validTarget :
      (Dyck.oneFace
        (targetWord first second
          hfirstSecond tail)).IsSurfaceValid :=
    isSurfaceValid_of_p1Expand _ _ validExpansion
  have hsign :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord first second
            firstNegative secondNegative tail),
          validSource⟩
        ⟨Dyck.oneFace
          (sourceWord first second false false tail),
          validPositiveSource⟩ :=
    NormalizationEquivalent.ofSignedIso signIso
  have hexpansion :
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (sourceWord first second false false tail),
          validPositiveSource⟩
        ⟨P1.expand
          (Dyck.oneFace
            (targetWord first second
              hfirstSecond tail))
          (Cancellation.lowerEdge second first
            hfirstSecond),
          validExpansion⟩ :=
    NormalizationEquivalent.ofSignedIso expansionIso
  have hcontraction :
      NormalizationEquivalent
        ⟨P1.expand
          (Dyck.oneFace
            (targetWord first second
              hfirstSecond tail))
          (Cancellation.lowerEdge second first
            hfirstSecond),
          validExpansion⟩
        ⟨Dyck.oneFace
          (targetWord first second
            hfirstSecond tail),
          validTarget⟩ := by
    simpa only using
      (P1.contractionNormalizationEquivalent
        (Dyck.oneFace
          (targetWord first second
            hfirstSecond tail))
        (Cancellation.lowerEdge second first
          hfirstSecond)
        validTarget)
  exact
    ⟨validTarget,
      hsign.trans
        (hexpansion.trans hcontraction)⟩

end BoundaryPairContraction

namespace BoundaryEnvelope

/-- A one-face word before a fresh opposite carrier pair is introduced. -/
@[reducible]
def source {n : ℕ} (word : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace word

/-- The fresh carrier name in the enlarged edge type. -/
def carrier (n : ℕ) : Fin (n + 1) :=
  P1.freshEdge n

/-- Enclose a retained word in a fresh positively oriented carrier pair. -/
def targetWord {n : ℕ} (word : List (SignedDart (Fin n))) :
    List (SignedDart (Fin (n + 1))) :=
  [.pos (carrier n)] ++ P2.retainWord word ++
    [.neg (carrier n)]

/-- The `target` declaration. -/
@[reducible]
def target {n : ℕ} (word : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (targetWord word)

/-- The one-sided source split creates the carrier as a face separator. -/
def sourceCut {n : ℕ} (word : List (SignedDart (Fin n))) :
    P2Cut (source word) where
  face := .pos 0
  left := []
  right := word
  boundary_rotated := List.IsRotated.refl _

/-- Split the enveloped target between its two carrier occurrences. -/
def targetCut {n : ℕ} (word : List (SignedDart (Fin n))) :
    P2Cut (target word) where
  face := .pos 0
  left := [.neg (carrier n)]
  right := [.pos (carrier n)] ++ P2.retainWord word
  boundary_rotated := by
    change
      (targetWord word).IsRotated
        ([.neg (carrier n)] ++
          ([.pos (carrier n)] ++ P2.retainWord word))
    convert
      (List.isRotated_append
        (l := [.pos (carrier n)] ++ P2.retainWord word)
        (l' := [.neg (carrier n)])) using 1 ;
      simp [targetWord, List.cons_append]

/-- The right side of the enveloped cut contains the positive carrier followed by the retained
word. -/
@[simp]
private theorem targetCut_right {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    (targetCut word).right =
      [.pos (carrier n)] ++ P2.retainWord word :=
  rfl

/-- The separator edge selected for P1 expansion in the source split. -/
def expandedCarrier {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    (P2.split (source word) (sourceCut word)).Edge :=
  P2.freshEdge (source word)

/-- The retained half of the expanded source separator. -/
def subdivisionCarrier {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    (P1.expand
      (P2.split (source word) (sourceCut word))
      (expandedCarrier word)).Edge :=
  (expandedCarrier word).castSucc

/-- Reverse the retained separator when identifying the two common subdivisions. -/
def subdivisionRelabeling {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    EdgeRelabeling
      (P1.expand
        (P2.split (source word) (sourceCut word))
        (expandedCarrier word)).Edge
      (P2.split (target word) (targetCut word)).Edge :=
  Dyck.reverseEdgeRelabeling (subdivisionCarrier word)

/-- The `subdivisionFaceEquiv` declaration. -/
def subdivisionFaceEquiv {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    (P1.expand
      (P2.split (source word) (sourceCut word))
      (expandedCarrier word)).Face ≃
      (P2.split (target word) (targetCut word)).Face :=
  (P1.faceEquiv
      (P2.split (source word) (sourceCut word))
      (expandedCarrier word)).symm |>.trans
    ((P2.faceEquiv (source word) (sourceCut word)).symm.trans
      (P2.faceEquiv (target word) (targetCut word)))

/-- Expanding the source separator and splitting the enveloped target give signed-isomorphic
two-face presentations. -/
def subdivisionSignedIso {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    SignedPresentationIso
      (P1.expand
        (P2.split (source word) (sourceCut word))
        (expandedCarrier word))
      (P2.split (target word) (targetCut word)) where
  edgeRelabeling := subdivisionRelabeling word
  faceEquiv := subdivisionFaceEquiv word
  boundary_rotated := by
    intro f
    let sourceSplit :=
      P2.split (source word) (sourceCut word)
    let a := expandedCarrier word
    obtain ⟨sf, rfl⟩ :=
      (P1.faceEquiv sourceSplit a).surjective f
    obtain ⟨i, rfl⟩ :=
      (P2.faceEquiv (source word)
        (sourceCut word)).surjective sf
    rw [P1.expand_boundary]
    induction i using Fin.lastCases with
    | last =>
      change
        ((P1.expandWord a
            ((P2.split (source word) (sourceCut word)).boundary
              (P2.rightFace (source word) (sourceCut word)))).map
          (subdivisionRelabeling word).mapDart).IsRotated
          ((P2.split (target word) (targetCut word)).boundary
            (P2.rightFace (target word) (targetCut word)))
      rw [P2.split_boundary_right,
        P2.split_boundary_right]
      change
        ((P1.expandWord (Fin.last n)
            (.neg (Fin.last n) ::
              P2.retainWord word)).map
          (Dyck.reverseEdgeRelabeling
            (Fin.last n).castSucc).mapDart).IsRotated
          (.neg (Fin.last (n + 1)) ::
            .pos (Fin.last n).castSucc ::
              P2.retainWord (P2.retainWord word))
      rw [P1.expandWord_cons,
        P1.expandDart_neg_self]
      have hexpand :=
        Cancellation.expandWord_retainWord_fresh word
      change
        P1.expandWord (Fin.last n)
            (P2.retainWord word) =
          P2.retainWord (P2.retainWord word) at hexpand
      rw [hexpand]
      simp only [P1.firstSubedge, P1.freshEdge,
        List.map_append, List.map_cons, List.map_nil]
      have hfresh :
          Fin.last (n + 1) ≠ (Fin.last n).castSucc :=
        (Fin.castSucc_ne_last (Fin.last n)).symm
      have hfreshNeg :
          (Dyck.reverseEdgeRelabeling
              (Fin.last n).castSucc).mapDart
              (.neg (Fin.last (n + 1))) =
            .neg (Fin.last (n + 1)) := by
        simpa using
          (Dyck.reverseEdgeRelabeling_of_ne
            (Fin.last n).castSucc (Fin.last (n + 1))
            hfresh true)
      rw [hfreshNeg, Dyck.reverseEdgeRelabeling_neg]
      have hcarrierTail :
          (Fin.last n).castSucc ∉
            (P2.retainWord
              (P2.retainWord word)).map edgeOfDart := by
        simp [P2.retainWord]
      rw [Dyck.reverseEdgeRelabeling_word
        (Fin.last n).castSucc
        (P2.retainWord (P2.retainWord word))
        hcarrierTail]
      exact List.IsRotated.refl _
    | cast i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change
        ((P1.expandWord a
            ((P2.split (source word) (sourceCut word)).boundary
              (P2.oldFace (source word) (sourceCut word)
                (sourceCut word).face.face))).map
          (subdivisionRelabeling word).mapDart).IsRotated
          ((P2.split (target word) (targetCut word)).boundary
            (P2.oldFace (target word) (targetCut word)
              (targetCut word).face.face))
      rw [P2.split_boundary_selected,
        P2.split_boundary_selected]
      change
        ((P1.expandWord (Fin.last n)
            [.pos (Fin.last n)]).map
          (Dyck.reverseEdgeRelabeling
            (Fin.last n).castSucc).mapDart).IsRotated
          [.neg (Fin.last n).castSucc,
            .pos (Fin.last (n + 1))]
      rw [P1.expandWord_cons,
        P1.expandDart_pos_self]
      simp only [P1.expandWord_nil,
        List.append_nil, List.map_cons, List.map_nil,
        P1.firstSubedge, P1.freshEdge]
      have hfresh :
          Fin.last (n + 1) ≠ (Fin.last n).castSucc :=
        (Fin.castSucc_ne_last (Fin.last n)).symm
      have hfreshPos :
          (Dyck.reverseEdgeRelabeling
              (Fin.last n).castSucc).mapDart
              (.pos (Fin.last (n + 1))) =
            .pos (Fin.last (n + 1)) := by
        simpa using
          (Dyck.reverseEdgeRelabeling_of_ne
            (Fin.last n).castSucc (Fin.last (n + 1))
            hfresh false)
      rw [Dyck.reverseEdgeRelabeling_pos,
        hfreshPos]

/-- The enveloping carrier adds one twice-used name and retains all old multiplicities. -/
theorem target_isSurfaceValid {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (validSource : (source word).IsSurfaceValid) :
    (target word).IsSurfaceValid := by
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    simp [target, targetWord]
  · intro f g _
    rw [Dyck.oneFace_face_eq_zero (targetWord word) f,
      Dyck.oneFace_face_eq_zero (targetWord word) g]
  · intro e
    induction e using Fin.lastCases with
    | last =>
      rw [Dyck.oneFace_edgeMultiplicity]
      simp only [targetWord, carrier, P1.freshEdge, P2.retainWord,
        List.cons_append, List.nil_append, List.map_cons, edgeOfDart_pos,
        List.map_append, List.map_map, Function.comp_def,
        P1.edgeOfDart_castSuccDart, edgeOfDart_neg, List.map_nil,
        List.count_cons_self, List.count_append, List.nodup_cons,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
        List.mem_cons, or_false, List.count_eq_one_of_mem, Nat.add_eq_right,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.reduceEqDiff, false_or]
      apply List.count_eq_zero.mpr
      intro hmem
      rcases List.mem_map.mp hmem with
        ⟨d, _, hd⟩
      exact Fin.castSucc_ne_last (edgeOfDart d)
        hd
    | cast e =>
      have hmultiplicity := validSource.2.2.2 e
      rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity ⊢
      simp only [targetWord, List.map_append,
        List.map_cons, List.map_nil, edgeOfDart,
        List.count_cons, List.count_append,
        List.count_nil]
      rw [P2.count_retainWord_castSucc]
      have hne :
          e.castSucc ≠ carrier n := by
        exact P1.firstSubedge_ne_freshEdge e
      simp only [beq_iff_eq, hne.symm, ↓reduceIte, add_zero, zero_add]
      exact hmultiplicity

theorem sourceCut_isOneSided {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (hne : word ≠ []) :
    ((sourceCut word).left = [] ∧
        0 < (sourceCut word).right.length) ∨
      (0 < (sourceCut word).left.length ∧
        (sourceCut word).right = []) :=
  Or.inl ⟨rfl, List.length_pos_iff_ne_nil.mpr hne⟩

theorem targetCut_isNondegenerate {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    (targetCut word).IsNondegenerate := by
  constructor <;> simp [targetCut]

/-- Add a fresh opposite carrier pair around a nonempty one-face word.  A one-sided P2 split
followed by P1 has the same subdivision as a genuine split of the enveloped target. -/
theorem normalizationEquivalent {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (hne : word ≠ [])
    (validSource : (source word).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source word, validSource⟩
      ⟨target word,
        target_isSurfaceValid word validSource⟩ := by
  let sourceSplit :=
    P2.split (source word) (sourceCut word)
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid
      (source word) (sourceCut word) validSource
  let sourceExpanded :=
    P1.expand sourceSplit (expandedCarrier word)
  let validSourceExpanded :
      sourceExpanded.IsSurfaceValid :=
    P1.expand_isSurfaceValid sourceSplit
      (expandedCarrier word) validSourceSplit
  let validTarget :=
    target_isSurfaceValid word validSource
  let targetSplit :=
    P2.split (target word) (targetCut word)
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid
      (target word) (targetCut word) validTarget
  have hSourceSplit :
      NormalizationEquivalent
        ⟨source word, validSource⟩
        ⟨sourceSplit, validSourceSplit⟩ :=
    NormalizationEquivalent.ofOneSidedP2
      (P := ⟨source word, validSource⟩)
      (sourceCut word) (sourceCut_isOneSided word hne)
  have hExpand :
      NormalizationEquivalent
        ⟨sourceSplit, validSourceSplit⟩
        ⟨sourceExpanded, validSourceExpanded⟩ :=
    NormalizationEquivalent.ofP1
      (P1Subdivision.canonical
        sourceSplit (expandedCarrier word))
  have hIso :
      NormalizationEquivalent
        ⟨sourceExpanded, validSourceExpanded⟩
        ⟨targetSplit, validTargetSplit⟩ :=
    NormalizationEquivalent.ofSignedIso
      (subdivisionSignedIso word)
  have hMerge :
      NormalizationEquivalent
        ⟨targetSplit, validTargetSplit⟩
        ⟨target word, validTarget⟩ :=
    P2.mergeNormalizationEquivalent
      (target word) (targetCut word)
      (targetCut_isNondegenerate word) validTarget
  exact hSourceSplit.trans
    (hExpand.trans (hIso.trans hMerge))

end BoundaryEnvelope

/-- One non-residual atom allowed in a classified marked execution state. -/
inductive ProtectedAtom (n : ℕ)
  | boundary (hole : Fin n) (negative : Bool)
  | completed (block : CompletedBlock n)

namespace ProtectedAtom

/-- Exact signed word represented by one classified protected atom. -/
def word {n : ℕ} : ProtectedAtom n →
    List (SignedDart (Fin n))
  | .boundary hole negative =>
      [dart hole negative]
  | .completed block =>
      block.word

/-- Edge names protected by one classified atom. -/
def edges {n : ℕ} : ProtectedAtom n → List (Fin n)
  | .boundary hole _ => [hole]
  | .completed block => block.edges

/-- Distinct protected names owned by one classified atom. -/
def names {n : ℕ} : ProtectedAtom n → List (Fin n)
  | .boundary hole _ => [hole]
  | .completed block => block.names

/-- Retain a completed block when one fresh ambient carrier name is added. -/
def retainCompleted {n : ℕ} :
    CompletedBlock n → CompletedBlock (n + 1)
  | .crosscap a negative =>
      .crosscap a.castSucc negative
  | .handle a b =>
      .handle a.castSucc b.castSucc
  | .boundary carrier hole carrierNegative holeNegative =>
      .boundary carrier.castSucc hole.castSucc
        carrierNegative holeNegative

/-- Retain a protected atom when one fresh ambient carrier name is added. -/
def retain {n : ℕ} :
    ProtectedAtom n → ProtectedAtom (n + 1)
  | .boundary hole negative =>
      .boundary hole.castSucc negative
  | .completed block =>
      .completed (retainCompleted block)

/-- Reverse one protected atom. -/
def inverse {n : ℕ} : ProtectedAtom n → ProtectedAtom n
  | .boundary hole negative =>
      .boundary hole (!negative)
  | .completed block =>
      .completed block.inverse

/-- Concatenate a protected atom sequence into its exact signed word. -/
def sequenceWord {n : ℕ} (atoms : List (ProtectedAtom n)) :
    List (SignedDart (Fin n)) :=
  (atoms.map word).flatten

/-- Concatenate the distinct-name spines owned by a protected atom sequence. -/
def sequenceNames {n : ℕ} (atoms : List (ProtectedAtom n)) :
    List (Fin n) :=
  (atoms.map names).flatten

@[simp]
theorem sequenceNames_cons {n : ℕ}
    (head : ProtectedAtom n)
    (tail : List (ProtectedAtom n)) :
    sequenceNames (head :: tail) =
      head.names ++ sequenceNames tail :=
  rfl

/-- Reverse a protected atom sequence at atom granularity. -/
def inverseSequence {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    List (ProtectedAtom n) :=
  (atoms.map inverse).reverse

@[simp]
theorem word_inverse {n : ℕ} (atom : ProtectedAtom n) :
    atom.inverse.word = inverseWord atom.word := by
  cases atom with
  | boundary hole negative =>
      cases negative <;> rfl
  | completed block =>
      exact CompletedBlock.word_inverse block

@[simp]
theorem sequenceWord_nil {n : ℕ} :
    sequenceWord ([] : List (ProtectedAtom n)) = [] :=
  rfl

@[simp]
theorem sequenceWord_cons {n : ℕ}
    (atom : ProtectedAtom n)
    (atoms : List (ProtectedAtom n)) :
    sequenceWord (atom :: atoms) =
      atom.word ++ sequenceWord atoms := by
  simp [sequenceWord]

@[simp]
theorem sequenceWord_append {n : ℕ}
    (left right : List (ProtectedAtom n)) :
    sequenceWord (left ++ right) =
      sequenceWord left ++ sequenceWord right := by
  simp [sequenceWord]

@[simp]
theorem sequenceWord_inverseSequence {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    sequenceWord (inverseSequence atoms) =
      inverseWord (sequenceWord atoms) := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rw [show inverseSequence (atom :: atoms) =
          inverseSequence atoms ++ [atom.inverse] by
        simp [inverseSequence]]
      rw [sequenceWord_append, ih]
      simp [inverseWord_append]

@[simp]
theorem word_retainCompleted {n : ℕ}
    (block : CompletedBlock n) :
    (retainCompleted block).word =
      P2.retainWord block.word := by
  cases block with
  | crosscap a negative =>
      cases negative <;>
        simp [retainCompleted, CompletedBlock.word,
          P2.retainWord, dart]
  | handle =>
      simp [retainCompleted, CompletedBlock.word,
        P2.retainWord]
  | boundary carrier hole carrierNegative holeNegative =>
      cases carrierNegative <;>
        cases holeNegative <;>
          simp [retainCompleted, CompletedBlock.word,
            boundaryLoopWord, P2.retainWord, dart]

@[simp]
theorem names_retainCompleted {n : ℕ}
    (block : CompletedBlock n) :
    (retainCompleted block).names =
      block.names.map Fin.castSucc := by
  cases block <;> rfl

@[simp]
theorem word_retain {n : ℕ}
    (atom : ProtectedAtom n) :
    atom.retain.word =
      P2.retainWord atom.word := by
  cases atom with
  | boundary hole negative =>
      cases negative <;>
        simp [retain, word, P2.retainWord, dart]
  | completed block =>
      exact word_retainCompleted block

@[simp]
theorem names_retain {n : ℕ}
    (atom : ProtectedAtom n) :
    atom.retain.names =
      atom.names.map Fin.castSucc := by
  cases atom with
  | boundary => rfl
  | completed block =>
      exact names_retainCompleted block

@[simp]
theorem sequenceWord_map_retain {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    sequenceWord (atoms.map retain) =
      P2.retainWord (sequenceWord atoms) := by
  induction atoms with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [ih]

@[simp]
theorem sequenceNames_map_retain {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    sequenceNames (atoms.map retain) =
      (sequenceNames atoms).map Fin.castSucc := by
  induction atoms with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.map_cons, sequenceNames_cons,
        names_retain, ih, List.map_append]

/-- Number of raw once-used boundary darts.  Terminal normalization groups and contracts every
such dart to one representative of the remaining outer boundary component. -/
def rawBoundaryCount {n : ℕ} :
    List (ProtectedAtom n) → ℕ
  | [] => 0
  | .boundary _ _ :: atoms => 1 + rawBoundaryCount atoms
  | _ :: atoms => rawBoundaryCount atoms

/-- Number of boundary components already displayed as completed carrier loops. -/
def completedBoundaryCount {n : ℕ} :
    List (ProtectedAtom n) → ℕ
  | [] => 0
  | .completed (.boundary _ _ _ _) :: atoms =>
      1 + completedBoundaryCount atoms
  | _ :: atoms => completedBoundaryCount atoms

/-- Number of boundary components selected by a terminal atom sequence.  Completed loops are
already distinct boundary components.  All remaining raw boundary darts lie on the one outer
boundary component and therefore contribute one component collectively, rather than one each. -/
def boundaryCount {n : ℕ}
    (atoms : List (ProtectedAtom n)) : ℕ :=
  completedBoundaryCount atoms +
    if rawBoundaryCount atoms = 0 then 0 else 1

/-- Number of completed crosscap blocks. -/
def crosscapCount {n : ℕ} :
    List (ProtectedAtom n) → ℕ
  | [] => 0
  | .completed (.crosscap _ _) :: atoms =>
      1 + crosscapCount atoms
  | _ :: atoms => crosscapCount atoms

/-- Number of completed handle blocks. -/
def handleCount {n : ℕ} :
    List (ProtectedAtom n) → ℕ
  | [] => 0
  | .completed (.handle _ _) :: atoms =>
      1 + handleCount atoms
  | _ :: atoms => handleCount atoms

/-- Normal-form parameters selected by a terminal protected-atom sequence.  Completed boundary
loops contribute individually; any remaining raw boundary darts collectively contribute the one
outer boundary component and will be grouped during terminal normalization. -/
def normalForm {n : ℕ}
    (atoms : List (ProtectedAtom n)) : NormalForm :=
  if crosscapCount atoms = 0 then
    .orientable (handleCount atoms) (boundaryCount atoms)
  else
    .nonOrientable
      (crosscapCount atoms + 2 * handleCount atoms)
      (boundaryCount atoms)

/-- Every protected atom is raw boundary data or belongs to exactly one completed block class. -/
theorem raw_completed_count_sum_eq_length {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    rawBoundaryCount atoms + completedBoundaryCount atoms +
        crosscapCount atoms +
        handleCount atoms =
      atoms.length := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      cases atom with
      | boundary =>
          simp only [rawBoundaryCount, completedBoundaryCount,
            crosscapCount, handleCount, List.length_cons] at ih ⊢
          omega
      | completed block =>
          cases block <;>
            simp only [rawBoundaryCount, completedBoundaryCount,
              crosscapCount, handleCount, List.length_cons] at ih ⊢ <;>
            omega

/-- A nonempty terminal protected-atom sequence selects an Eval-admissible normal form. -/
theorem normalForm_isEvalAdmissible_of_ne_nil {n : ℕ}
    (atoms : List (ProtectedAtom n))
    (hne : atoms ≠ []) :
    (normalForm atoms).IsEvalAdmissible := by
  have hlength : 0 < atoms.length :=
    List.length_pos_iff_ne_nil.mpr hne
  have hsum := raw_completed_count_sum_eq_length atoms
  simp only [normalForm]
  split_ifs with hcrosscap
  · change 1 ≤ handleCount atoms ∨
      1 ≤ boundaryCount atoms
    rw [hcrosscap] at hsum
    by_cases hhandle : handleCount atoms = 0
    · right
      simp only [boundaryCount]
      by_cases hraw : rawBoundaryCount atoms = 0
      · rw [if_pos hraw]
        omega
      · rw [if_neg hraw]
        omega
    · left
      omega
  · change
      1 ≤ crosscapCount atoms +
        2 * handleCount atoms
    omega

/-- A protected atom sequence with no raw boundary singleton consists entirely of completed
blocks. -/
theorem exists_eq_map_completed_of_rawBoundaryCount_eq_zero
    {n : ℕ} (atoms : List (ProtectedAtom n))
    (hraw : rawBoundaryCount atoms = 0) :
    ∃ blocks : List (CompletedBlock n),
      atoms = blocks.map .completed := by
  induction atoms with
  | nil =>
      exact ⟨[], rfl⟩
  | cons atom atoms ih =>
      cases atom with
      | boundary =>
          simp [rawBoundaryCount] at hraw
      | completed block =>
          have htail :
              rawBoundaryCount atoms = 0 := by
            simpa [rawBoundaryCount] using hraw
          rcases ih htail with ⟨blocks, rfl⟩
          exact ⟨block :: blocks, rfl⟩

@[simp]
theorem sequenceWord_map_completed {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    sequenceWord (blocks.map .completed) =
      CompletedBlock.sequenceWord blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      simp [ih, word]

@[simp]
theorem sequenceNames_map_completed {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    sequenceNames (blocks.map .completed) =
      CompletedBlock.sequenceNames blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      simp [ih, names]

end ProtectedAtom

/-- A marked normalization word.  Residual darts are still available to subsequent pairing
reductions; extracted blocks are atomic tokens whose exact dart succession must be preserved. -/
inductive ReductionToken (n : ℕ)
  | residual (dart : SignedDart (Fin n))
  | extracted (block : ExtractedBlock n)
  | completed (block : CompletedBlock n)

namespace ReductionToken

/-- Embed a classified protected atom as one marked token. -/
def ofProtectedAtom {n : ℕ} :
    ProtectedAtom n → ReductionToken n
  | .boundary hole negative =>
      .extracted (.boundary hole negative)
  | .completed block =>
      .completed block

/-- Number of still-raw boundary singleton tokens in a marked word. -/
def rawBoundaryCount {n : ℕ} :
    List (ReductionToken n) → ℕ
  | [] => 0
  | .extracted (.boundary _ _) :: tokens =>
      1 + rawBoundaryCount tokens
  | _ :: tokens =>
      rawBoundaryCount tokens

@[simp]
theorem rawBoundaryCount_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    rawBoundaryCount (left ++ right) =
      rawBoundaryCount left + rawBoundaryCount right := by
  induction left with
  | nil =>
      simp [rawBoundaryCount]
  | cons token tokens ih =>
      cases token with
      | residual =>
          simpa [rawBoundaryCount] using ih
      | extracted block =>
          cases block <;>
            simp [rawBoundaryCount, ih] ;
            omega
      | completed =>
          simpa [rawBoundaryCount] using ih

@[simp]
theorem rawBoundaryCount_map_ofProtectedAtom {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    rawBoundaryCount (atoms.map ofProtectedAtom) =
      ProtectedAtom.rawBoundaryCount atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      cases atom with
      | boundary =>
          simp [rawBoundaryCount,
            ProtectedAtom.rawBoundaryCount, ofProtectedAtom, ih]
      | completed block =>
          simp [rawBoundaryCount,
            ProtectedAtom.rawBoundaryCount, ofProtectedAtom, ih]

/-- Exact signed word represented by one marked token. -/
def word {n : ℕ} : ReductionToken n →
    List (SignedDart (Fin n))
  | .residual dart => [dart]
  | .extracted block => block.word
  | .completed block => block.word

/-- Residual contribution of one marked token. -/
def residualWord {n : ℕ} : ReductionToken n →
    List (SignedDart (Fin n))
  | .residual dart => [dart]
  | .extracted _ => []
  | .completed _ => []

/-- Edge names protected inside one extracted-block token. -/
def extractedEdges {n : ℕ} : ReductionToken n → List (Fin n)
  | .residual _ => []
  | .extracted block => block.edges
  | .completed block => block.edges

/-- One occurrence of every protected edge name represented by a token. -/
def extractedNames {n : ℕ} : ReductionToken n → List (Fin n)
  | .residual _ => []
  | .extracted block => block.edges
  | .completed block => block.names

@[simp]
theorem word_residual {n : ℕ} (dart : SignedDart (Fin n)) :
    word (.residual dart) = [dart] :=
  rfl

@[simp]
theorem word_extracted {n : ℕ} (block : ExtractedBlock n) :
    word (.extracted block) = block.word :=
  rfl

@[simp]
theorem word_completed {n : ℕ}
    (block : CompletedBlock n) :
    word (.completed block) = block.word :=
  rfl

@[simp]
theorem residualWord_residual {n : ℕ}
    (dart : SignedDart (Fin n)) :
    residualWord (.residual dart) = [dart] :=
  rfl

@[simp]
theorem residualWord_extracted {n : ℕ}
    (block : ExtractedBlock n) :
    residualWord (.extracted block) = [] :=
  rfl

@[simp]
theorem residualWord_completed {n : ℕ}
    (block : CompletedBlock n) :
    residualWord (.completed block) = [] :=
  rfl

@[simp]
theorem extractedEdges_residual {n : ℕ}
    (dart : SignedDart (Fin n)) :
    extractedEdges (.residual dart) = [] :=
  rfl

@[simp]
theorem extractedEdges_extracted {n : ℕ}
    (block : ExtractedBlock n) :
    extractedEdges (.extracted block) = block.edges :=
  rfl

@[simp]
theorem extractedEdges_completed {n : ℕ}
    (block : CompletedBlock n) :
    extractedEdges (.completed block) =
      block.edges :=
  rfl

@[simp]
theorem extractedNames_residual {n : ℕ}
    (dart : SignedDart (Fin n)) :
    extractedNames (.residual dart) = [] :=
  rfl

@[simp]
theorem extractedNames_extracted {n : ℕ}
    (block : ExtractedBlock n) :
    extractedNames (.extracted block) = block.edges :=
  rfl

@[simp]
theorem extractedNames_completed {n : ℕ}
    (block : CompletedBlock n) :
    extractedNames (.completed block) = block.names :=
  rfl

@[simp]
theorem mem_extractedNames_iff_mem_extractedEdges {n : ℕ}
    (token : ReductionToken n) (a : Fin n) :
    a ∈ token.extractedNames ↔ a ∈ token.extractedEdges := by
  cases token with
  | residual => simp
  | extracted => rfl
  | completed block =>
      exact CompletedBlock.mem_names_iff_mem_edges block a

/-- Structural grammar of marked execution states.  Extracted crosscaps and handles are promoted
immediately to completed blocks; only a boundary singleton may remain in the intermediate
`extracted` constructor. -/
def IsClassified {n : ℕ} : ReductionToken n → Prop
  | .residual _ => True
  | .extracted (.boundary _ _) => True
  | .extracted _ => False
  | .completed _ => True

/-- Every token in a marked execution state obeys the classified-token grammar. -/
def AllClassified {n : ℕ}
    (tokens : List (ReductionToken n)) : Prop :=
  ∀ token ∈ tokens, token.IsClassified

@[simp]
theorem isClassified_residual {n : ℕ}
    (d : SignedDart (Fin n)) :
    IsClassified (.residual d) :=
  trivial

@[simp]
theorem isClassified_boundary {n : ℕ}
    (a : Fin n) (negative : Bool) :
    IsClassified (.extracted (.boundary a negative)) :=
  trivial

@[simp]
theorem isClassified_completed {n : ℕ}
    (block : CompletedBlock n) :
    IsClassified (.completed block) :=
  trivial

@[simp]
theorem isClassified_ofProtectedAtom {n : ℕ}
    (atom : ProtectedAtom n) :
    IsClassified (ofProtectedAtom atom) := by
  cases atom <;> trivial

@[simp]
theorem word_ofProtectedAtom {n : ℕ}
    (atom : ProtectedAtom n) :
    word (ofProtectedAtom atom) = atom.word := by
  cases atom <;> rfl

@[simp]
theorem residualWord_ofProtectedAtom {n : ℕ}
    (atom : ProtectedAtom n) :
    residualWord (ofProtectedAtom atom) = [] := by
  cases atom <;> rfl

@[simp]
theorem extractedEdges_ofProtectedAtom {n : ℕ}
    (atom : ProtectedAtom n) :
    extractedEdges (ofProtectedAtom atom) = atom.edges := by
  cases atom <;> rfl

@[simp]
theorem extractedNames_ofProtectedAtom {n : ℕ}
    (atom : ProtectedAtom n) :
    extractedNames (ofProtectedAtom atom) = atom.names := by
  cases atom <;> rfl

theorem AllClassified.of_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (classified : AllClassified tokens)
    (rotated : tokens.IsRotated target) :
    AllClassified target := by
  intro token htoken
  exact classified token
    (rotated.perm.mem_iff.mpr htoken)

theorem AllClassified.of_perm {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (classified : AllClassified tokens)
    (permuted : tokens.Perm target) :
    AllClassified target := by
  intro token htoken
  exact classified token
    (permuted.mem_iff.mpr htoken)

theorem AllClassified.of_append_left {n : ℕ}
    {left right : List (ReductionToken n)}
    (classified : AllClassified (left ++ right)) :
    AllClassified left := by
  intro token htoken
  exact classified token (by simp [htoken])

theorem AllClassified.of_append_right {n : ℕ}
    {left right : List (ReductionToken n)}
    (classified : AllClassified (left ++ right)) :
    AllClassified right := by
  intro token htoken
  exact classified token (by simp [htoken])

theorem AllClassified.append {n : ℕ}
    {left right : List (ReductionToken n)}
    (leftClassified : AllClassified left)
    (rightClassified : AllClassified right) :
    AllClassified (left ++ right) := by
  intro token htoken
  rcases List.mem_append.mp htoken with hleft | hright
  · exact leftClassified token hleft
  · exact rightClassified token hright

@[simp]
theorem allClassified_cons {n : ℕ}
    (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    AllClassified (token :: tokens) ↔
      token.IsClassified ∧ AllClassified tokens := by
  simp [AllClassified]

/-- Reverse a token while preserving an extracted block as one atomic token. -/
def inverse {n : ℕ} : ReductionToken n → ReductionToken n
  | .residual dart => .residual dart.flip
  | .extracted block => .extracted block.inverse
  | .completed block =>
      .completed block.inverse

/-- Relabel every edge name represented by a marked token. -/
def mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m) :
    ReductionToken n → ReductionToken m
  | .residual dart => .residual (SignedDart.mapEquiv e dart)
  | .extracted block => .extracted (block.mapEquiv e)
  | .completed block =>
      .completed (block.mapEquiv e)

@[simp]
theorem inverse_ofProtectedAtom {n : ℕ}
    (atom : ProtectedAtom n) :
    inverse (ofProtectedAtom atom) =
      ofProtectedAtom atom.inverse := by
  cases atom <;> rfl

theorem IsClassified.inverse {n : ℕ}
    {token : ReductionToken n}
    (classified : token.IsClassified) :
    token.inverse.IsClassified := by
  cases token with
  | residual =>
      trivial
  | extracted block =>
      cases block with
      | boundary =>
          trivial
      | crosscap =>
          exact classified.elim
      | handle =>
          exact classified.elim
  | completed =>
      trivial

theorem IsClassified.mapEquiv {n m : ℕ}
    {token : ReductionToken n}
    (classified : token.IsClassified)
    (e : Fin n ≃ Fin m) :
    (token.mapEquiv e).IsClassified := by
  cases token with
  | residual =>
      trivial
  | extracted block =>
      cases block with
      | boundary =>
          trivial
      | crosscap =>
          exact classified.elim
      | handle =>
          exact classified.elim
  | completed =>
      trivial

@[simp]
theorem word_inverse {n : ℕ} (token : ReductionToken n) :
    token.inverse.word = inverseWord token.word := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted block =>
      exact ExtractedBlock.word_inverse block
  | completed block =>
      exact CompletedBlock.word_inverse block

@[simp]
theorem residualWord_inverse {n : ℕ}
    (token : ReductionToken n) :
    token.inverse.residualWord =
      inverseWord token.residualWord := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted =>
      rfl
  | completed =>
      rfl

@[simp]
theorem extractedEdges_inverse {n : ℕ}
    (token : ReductionToken n) :
    token.inverse.extractedEdges =
      token.extractedEdges.reverse := by
  cases token with
  | residual =>
      rfl
  | extracted block =>
      exact ExtractedBlock.edges_inverse block
  | completed block =>
      exact CompletedBlock.edges_inverse block

theorem extractedNames_inverse_perm {n : ℕ}
    (token : ReductionToken n) :
    token.inverse.extractedNames.Perm
      token.extractedNames := by
  cases token with
  | residual =>
      simp [inverse, extractedNames]
  | extracted block =>
      simp [inverse, extractedNames,
        ExtractedBlock.edges_inverse]
  | completed block =>
      exact CompletedBlock.names_inverse_perm block

@[simp]
theorem inverse_inverse {n : ℕ} (token : ReductionToken n) :
    token.inverse.inverse = token := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted block =>
      simp [inverse]
  | completed block =>
      simp [inverse]

@[simp]
theorem word_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (token : ReductionToken n) :
    (token.mapEquiv e).word =
      token.word.map (SignedDart.mapEquiv e) := by
  cases token with
  | residual =>
      rfl
  | extracted block =>
      exact ExtractedBlock.word_mapEquiv e block
  | completed block =>
      exact CompletedBlock.word_mapEquiv e block

@[simp]
theorem residualWord_mapEquiv {n m : ℕ}
    (e : Fin n ≃ Fin m) (token : ReductionToken n) :
    (token.mapEquiv e).residualWord =
      token.residualWord.map (SignedDart.mapEquiv e) := by
  cases token <;> rfl

@[simp]
theorem inverse_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (token : ReductionToken n) :
    (token.mapEquiv e).inverse =
      token.inverse.mapEquiv e := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted block =>
      simp [inverse, mapEquiv]
  | completed block =>
      simp [inverse, mapEquiv]

/-- Lower a marked token known not to use the removed ambient edge. -/
def lowerAvoiding {n : ℕ} (a : Fin (n + 1))
    (token : ReductionToken (n + 1))
    (ha : a ∉ token.word.map edgeOfDart) :
    ReductionToken n :=
  match token with
  | .residual d =>
      .residual
        (Cancellation.lowerDart a d (by
          intro hedge
          apply ha
          simp [hedge]))
  | .extracted block =>
      .extracted
        (block.lowerAvoiding a (by
          intro hblock
          apply ha
          exact
            (ExtractedBlock.mem_map_edgeOfDart_word_iff
              block a).mpr hblock))
  | .completed block =>
      .completed
        (block.lowerAvoiding a (by
          intro hblock
          apply ha
          exact
            (CompletedBlock.mem_map_edgeOfDart_word_iff
              block a).mpr hblock))

theorem lowerAvoiding_residual_dart {n : ℕ}
    (a e : Fin (n + 1)) (negative : Bool)
    (ha :
      a ∉
        (ReductionToken.word
          (.residual (dart e negative))).map edgeOfDart) :
    ReductionToken.lowerAvoiding a
        (.residual (dart e negative)) ha =
      .residual
        (dart
          (Cancellation.lowerEdge a e (by
            intro heq
            apply ha
            simp [heq]))
          negative) := by
  cases negative <;> rfl

/-- Lowering one marked token agrees with word-level cancellation lowering. -/
theorem word_lowerAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (token : ReductionToken (n + 1))
    (ha : a ∉ token.word.map edgeOfDart) :
    (token.lowerAvoiding a ha).word =
      Cancellation.lowerTail a token.word := by
  cases token with
  | residual d =>
      simpa only [lowerAvoiding, word,
        Cancellation.lowerWordAvoiding] using
        Cancellation.lowerWordAvoiding_eq_lowerTail
          a [d] ha
  | extracted block =>
      exact ExtractedBlock.word_lowerAvoiding a block _
  | completed block =>
      exact CompletedBlock.word_lowerAvoiding a block _

theorem IsClassified.lowerAvoiding {n : ℕ}
    (a : Fin (n + 1))
    {token : ReductionToken (n + 1)}
    (classified : token.IsClassified)
    (ha : a ∉ token.word.map edgeOfDart) :
    (token.lowerAvoiding a ha).IsClassified := by
  cases token with
  | residual =>
      trivial
  | extracted block =>
      cases block with
      | boundary =>
          trivial
      | crosscap =>
          exact classified.elim
      | handle =>
          exact classified.elim
  | completed =>
      trivial

/-- Re-embedding residual edge names after lowering one token recovers the old residual names. -/
theorem residualEdges_lowerAvoiding_map_restoreEdge {n : ℕ}
    (a : Fin (n + 1))
    (token : ReductionToken (n + 1))
    (ha : a ∉ token.word.map edgeOfDart) :
    ((token.lowerAvoiding a ha).residualWord.map
        edgeOfDart).map (Cancellation.restoreEdge a) =
      token.residualWord.map edgeOfDart := by
  cases token with
  | residual d =>
      change
        [Cancellation.restoreEdge a
          (edgeOfDart
            (Cancellation.lowerDart a d _))] =
          [edgeOfDart d]
      rw [Cancellation.restoreEdge_edgeOfDart_lowerDart]
  | extracted =>
      rfl
  | completed =>
      rfl

/-- Re-embedding protected edge names after lowering one token recovers the old protected names. -/
theorem extractedEdges_lowerAvoiding_map_restoreEdge {n : ℕ}
    (a : Fin (n + 1))
    (token : ReductionToken (n + 1))
    (ha : a ∉ token.word.map edgeOfDart) :
    (token.lowerAvoiding a ha).extractedEdges.map
        (Cancellation.restoreEdge a) =
      token.extractedEdges := by
  cases token with
  | residual =>
      rfl
  | extracted block =>
      exact
        ExtractedBlock.edges_lowerAvoiding_map_restoreEdge
          a block _
  | completed block =>
      exact
        CompletedBlock.edges_lowerAvoiding_map_restoreEdge
          a block _

/-- Re-embedding a lowered token's distinct protected names recovers its old name spine. -/
theorem extractedNames_lowerAvoiding_map_restoreEdge {n : ℕ}
    (a : Fin (n + 1))
    (token : ReductionToken (n + 1))
    (ha : a ∉ token.word.map edgeOfDart) :
    (token.lowerAvoiding a ha).extractedNames.map
        (Cancellation.restoreEdge a) =
      token.extractedNames := by
  cases token with
  | residual =>
      rfl
  | extracted block =>
      exact
        ExtractedBlock.edges_lowerAvoiding_map_restoreEdge
          a block _
  | completed block =>
      exact
        CompletedBlock.names_lowerAvoiding_map_restoreEdge
          a block _

/-- Expand a marked word to the exact signed word on which normalization moves act. -/
def expand {n : ℕ} (tokens : List (ReductionToken n)) :
    List (SignedDart (Fin n)) :=
  (tokens.map word).flatten

/-- Erase extracted blocks and retain only the darts still available to pairing reduction. -/
def residualDarts {n : ℕ} (tokens : List (ReductionToken n)) :
    List (SignedDart (Fin n)) :=
  (tokens.map residualWord).flatten

/-- All edge names protected inside extracted block tokens. -/
def protectedEdges {n : ℕ} (tokens : List (ReductionToken n)) :
    List (Fin n) :=
  (tokens.map extractedEdges).flatten

/-- Distinct-name spine of all protected tokens.  Each token contributes each of its edge names
once, so global `Nodup` expresses disjoint ownership of protected names. -/
def protectedNames {n : ℕ} (tokens : List (ReductionToken n)) :
    List (Fin n) :=
  (tokens.map extractedNames).flatten

/-- Residual darts and already-extracted blocks use disjoint ambient edge names. -/
def IsSeparated {n : ℕ} (tokens : List (ReductionToken n)) : Prop :=
  ((residualDarts tokens).map edgeOfDart).Disjoint
    (protectedEdges tokens)

/-- Reverse a marked word at token granularity. -/
def inverseSequence {n : ℕ} (tokens : List (ReductionToken n)) :
    List (ReductionToken n) :=
  (tokens.map inverse).reverse

@[simp]
theorem rawBoundaryCount_inverseSequence {n : ℕ}
    (tokens : List (ReductionToken n)) :
    rawBoundaryCount (inverseSequence tokens) =
      rawBoundaryCount tokens := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      rw [show inverseSequence (token :: tokens) =
          inverseSequence tokens ++ [token.inverse] by
        simp [inverseSequence]]
      rw [rawBoundaryCount_append, ih]
      cases token with
      | residual =>
          simp [rawBoundaryCount, inverse]
      | extracted block =>
          cases block <;>
            simp [rawBoundaryCount, inverse,
              ExtractedBlock.inverse] ;
            omega
      | completed =>
          simp [rawBoundaryCount, inverse]

/-- Initially every dart is still residual. -/
def ofWord {n : ℕ} (word : List (SignedDart (Fin n))) :
    List (ReductionToken n) :=
  word.map .residual

/-- A finished marked word contains only extracted block tokens. -/
def ofBlocks {n : ℕ} (blocks : List (ExtractedBlock n)) :
    List (ReductionToken n) :=
  blocks.map .extracted

theorem allClassified_ofWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    AllClassified (ofWord word) := by
  intro token htoken
  rcases List.mem_map.mp htoken with ⟨dart, _, rfl⟩
  trivial

theorem AllClassified.inverseSequence {n : ℕ}
    {tokens : List (ReductionToken n)}
    (classified : AllClassified tokens) :
    AllClassified (ReductionToken.inverseSequence tokens) := by
  intro token htoken
  rw [ReductionToken.inverseSequence,
    List.mem_reverse] at htoken
  rcases List.mem_map.mp htoken with
    ⟨sourceToken, hsource, rfl⟩
  exact (classified sourceToken hsource).inverse

@[simp]
theorem expand_nil {n : ℕ} :
    expand ([] : List (ReductionToken n)) = [] :=
  rfl

@[simp]
theorem expand_cons {n : ℕ} (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    expand (token :: tokens) =
      token.word ++ expand tokens := by
  simp [expand]

@[simp]
theorem expand_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    expand (left ++ right) = expand left ++ expand right := by
  simp [expand]

@[simp]
theorem expand_map_ofProtectedAtom {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    expand (atoms.map ofProtectedAtom) =
      ProtectedAtom.sequenceWord atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      simp [ProtectedAtom.sequenceWord, ih]

@[simp]
theorem residualDarts_nil {n : ℕ} :
    residualDarts ([] : List (ReductionToken n)) = [] :=
  rfl

@[simp]
theorem residualDarts_cons {n : ℕ} (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    residualDarts (token :: tokens) =
      token.residualWord ++ residualDarts tokens := by
  simp [residualDarts]

@[simp]
theorem residualDarts_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    residualDarts (left ++ right) =
      residualDarts left ++ residualDarts right := by
  simp [residualDarts]

/-- A classified token list with no residual darts is exactly a list of typed protected atoms. -/
theorem exists_eq_map_ofProtectedAtom_of_allClassified_of_residualDarts_eq_nil
    {n : ℕ} (tokens : List (ReductionToken n))
    (classified : AllClassified tokens)
    (residual_nil : residualDarts tokens = []) :
    ∃ atoms : List (ProtectedAtom n),
      tokens = atoms.map ofProtectedAtom := by
  induction tokens with
  | nil =>
      exact ⟨[], rfl⟩
  | cons token tokens ih =>
      have tokenClassified :
          token.IsClassified :=
        classified token (by simp)
      have tailClassified :
          AllClassified tokens := by
        intro tailToken htail
        exact classified tailToken (by simp [htail])
      cases token with
      | residual dart =>
          simp only [residualDarts_cons,
            residualWord_residual,
            List.singleton_append] at residual_nil
          exact (List.cons_ne_nil dart _ residual_nil).elim
      | extracted block =>
          cases block with
          | boundary hole negative =>
              have tailResidual :
                  residualDarts tokens = [] := by
                simpa only [residualDarts_cons,
                  residualWord_extracted,
                  List.nil_append] using residual_nil
              rcases ih tailClassified tailResidual with
                ⟨atoms, rfl⟩
              exact
                ⟨.boundary hole negative :: atoms, rfl⟩
          | crosscap =>
              exact tokenClassified.elim
          | handle =>
              exact tokenClassified.elim
      | completed block =>
          have tailResidual :
              residualDarts tokens = [] := by
            simpa only [residualDarts_cons,
              residualWord_completed,
              List.nil_append] using residual_nil
          rcases ih tailClassified tailResidual with
            ⟨atoms, rfl⟩
          exact ⟨.completed block :: atoms, rfl⟩

/-- Canonical atom-level view of a classified marked word whose residual contribution is empty. -/
noncomputable def terminalAtoms {n : ℕ}
    (tokens : List (ReductionToken n))
    (classified : AllClassified tokens)
    (residual_nil : residualDarts tokens = []) :
    List (ProtectedAtom n) :=
  Classical.choose
    (exists_eq_map_ofProtectedAtom_of_allClassified_of_residualDarts_eq_nil
      tokens classified residual_nil)

theorem eq_map_terminalAtoms {n : ℕ}
    (tokens : List (ReductionToken n))
    (classified : AllClassified tokens)
    (residual_nil : residualDarts tokens = []) :
    tokens =
      (terminalAtoms tokens classified residual_nil).map
        ofProtectedAtom :=
  Classical.choose_spec
    (exists_eq_map_ofProtectedAtom_of_allClassified_of_residualDarts_eq_nil
      tokens classified residual_nil)

@[simp]
theorem expand_eq_sequenceWord_terminalAtoms {n : ℕ}
    (tokens : List (ReductionToken n))
    (classified : AllClassified tokens)
    (residual_nil : residualDarts tokens = []) :
    expand tokens =
      ProtectedAtom.sequenceWord
        (terminalAtoms tokens classified residual_nil) := by
  calc
    expand tokens =
        expand
          ((terminalAtoms tokens classified residual_nil).map
            ofProtectedAtom) :=
      congrArg expand
        (eq_map_terminalAtoms tokens classified residual_nil)
    _ = ProtectedAtom.sequenceWord
          (terminalAtoms tokens classified residual_nil) :=
      expand_map_ofProtectedAtom _

theorem terminalAtoms_ne_nil_of_protectedNames_ne_nil {n : ℕ}
    (tokens : List (ReductionToken n))
    (classified : AllClassified tokens)
    (residual_nil : residualDarts tokens = [])
    (protected_nonempty : protectedNames tokens ≠ []) :
    terminalAtoms tokens classified residual_nil ≠ [] := by
  intro hatoms
  apply protected_nonempty
  rw [eq_map_terminalAtoms tokens classified residual_nil,
    hatoms]
  rfl

@[simp]
theorem protectedNames_map_ofProtectedAtom {n : ℕ}
    (atoms : List (ProtectedAtom n)) :
    protectedNames (atoms.map ofProtectedAtom) =
      ProtectedAtom.sequenceNames atoms := by
  rw [protectedNames, ProtectedAtom.sequenceNames,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro atom _
  exact extractedNames_ofProtectedAtom atom

@[simp]
theorem protectedEdges_nil {n : ℕ} :
    protectedEdges ([] : List (ReductionToken n)) = [] :=
  rfl

@[simp]
theorem protectedEdges_cons {n : ℕ}
    (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    protectedEdges (token :: tokens) =
      token.extractedEdges ++ protectedEdges tokens := by
  simp [protectedEdges]

@[simp]
theorem protectedEdges_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    protectedEdges (left ++ right) =
    protectedEdges left ++ protectedEdges right := by
  simp [protectedEdges]

@[simp]
theorem protectedNames_nil {n : ℕ} :
    protectedNames ([] : List (ReductionToken n)) = [] :=
  rfl

@[simp]
theorem protectedNames_cons {n : ℕ}
    (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    protectedNames (token :: tokens) =
      token.extractedNames ++ protectedNames tokens := by
  simp [protectedNames]

@[simp]
theorem protectedNames_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    protectedNames (left ++ right) =
      protectedNames left ++ protectedNames right := by
  simp [protectedNames]

/-- The distinct-name spine and occurrence-level protected list have identical membership. -/
theorem mem_protectedNames_iff_mem_protectedEdges {n : ℕ}
    (tokens : List (ReductionToken n)) (a : Fin n) :
    a ∈ protectedNames tokens ↔
      a ∈ protectedEdges tokens := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      simp only [protectedNames_cons, protectedEdges_cons,
        List.mem_append]
      rw [mem_extractedNames_iff_mem_extractedEdges, ih]

/-- Cancellation lowering distributes over concatenation. -/
theorem Cancellation.lowerTail_append {n : ℕ}
    (a : Fin (n + 1))
    (left right : List (SignedDart (Fin (n + 1)))) :
    Cancellation.lowerTail a (left ++ right) =
      Cancellation.lowerTail a left ++
        Cancellation.lowerTail a right := by
  simp [Cancellation.lowerTail, Cancellation.renamedTail]

/-- Lower every token in a marked word which avoids the removed edge. -/
def lowerTokensAvoiding {n : ℕ} (a : Fin (n + 1)) :
    (tokens : List (ReductionToken (n + 1))) →
      a ∉ (expand tokens).map edgeOfDart →
      List (ReductionToken n)
  | [], _ => []
  | token :: tokens, ha =>
      token.lowerAvoiding a (by
        intro htoken
        apply ha
        simp [htoken]) ::
        lowerTokensAvoiding a tokens (by
          intro htokens
          apply ha
          simp [htokens])

@[simp]
theorem rawBoundaryCount_lowerTokensAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    rawBoundaryCount (lowerTokensAvoiding a tokens ha) =
      rawBoundaryCount tokens := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      cases token with
      | residual =>
          simp [lowerTokensAvoiding, lowerAvoiding,
            rawBoundaryCount, ih]
      | extracted block =>
          cases block <;>
            simp [lowerTokensAvoiding, lowerAvoiding,
              ExtractedBlock.lowerAvoiding,
              rawBoundaryCount, ih]
      | completed block =>
          cases block <;>
            simp [lowerTokensAvoiding, lowerAvoiding,
              CompletedBlock.lowerAvoiding,
              rawBoundaryCount, ih]

/-- Marked cancellation lowering distributes over token concatenation. -/
theorem lowerTokensAvoiding_append {n : ℕ}
    (a : Fin (n + 1))
    (left right : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand (left ++ right)).map edgeOfDart) :
    lowerTokensAvoiding a (left ++ right) ha =
      lowerTokensAvoiding a left (by
        intro hleft
        apply ha
        simp [hleft]) ++
      lowerTokensAvoiding a right (by
        intro hright
        apply ha
        simp [hright]) := by
  induction left with
  | nil =>
      rfl
  | cons token left ih =>
      change
        token.lowerAvoiding a _ ::
            lowerTokensAvoiding a (left ++ right) _ =
          token.lowerAvoiding a _ ::
            (lowerTokensAvoiding a left _ ++
              lowerTokensAvoiding a right _)
      congr 1
      exact ih _

@[simp]
theorem length_lowerTokensAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    (lowerTokensAvoiding a tokens ha).length =
      tokens.length := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      change
        (token.lowerAvoiding a _ ::
          lowerTokensAvoiding a tokens _).length =
            (token :: tokens).length
      simpa only [List.length_cons] using
        congrArg Nat.succ (ih _)

theorem AllClassified.lowerTokensAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (classified : AllClassified tokens)
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    AllClassified
      (ReductionToken.lowerTokensAvoiding a tokens ha) := by
  induction tokens with
  | nil =>
      intro token htoken
      simp [ReductionToken.lowerTokensAvoiding] at htoken
  | cons token tokens ih =>
      change AllClassified
        (token.lowerAvoiding a _ ::
          ReductionToken.lowerTokensAvoiding a tokens _)
      rw [allClassified_cons]
      refine ⟨?_, ?_⟩
      · apply (classified token (by simp)).lowerAvoiding
      · apply ih
        intro sourceToken hsource
        exact classified sourceToken (by simp [hsource])

/-- Expanding a lowered marked word gives exactly the ordinary cancellation target word. -/
theorem expand_lowerTokensAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    expand (lowerTokensAvoiding a tokens ha) =
      Cancellation.lowerTail a (expand tokens) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      rw [show
        lowerTokensAvoiding a (token :: tokens) ha =
          token.lowerAvoiding a (by
            intro htoken
            apply ha
            simp [htoken]) ::
          lowerTokensAvoiding a tokens (by
            intro htokens
            apply ha
            simp [htokens]) by rfl]
      rw [expand_cons,
        token.word_lowerAvoiding,
        ih]
      rw [expand_cons,
        Cancellation.lowerTail_append]

/-- Re-embedding all residual edge names after lowering a marked word recovers the source
residual namespace exactly. -/
theorem residualEdges_lowerTokensAvoiding_map_restoreEdge
    {n : ℕ} (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    (((residualDarts
      (lowerTokensAvoiding a tokens ha)).map
        edgeOfDart).map (Cancellation.restoreEdge a)) =
      (residualDarts tokens).map edgeOfDart := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      rw [show
        lowerTokensAvoiding a (token :: tokens) ha =
          token.lowerAvoiding a (by
            intro htoken
            apply ha
            simp [htoken]) ::
          lowerTokensAvoiding a tokens (by
            intro htokens
            apply ha
            simp [htokens]) by rfl]
      simp only [residualDarts_cons, List.map_append]
      rw [token.residualEdges_lowerAvoiding_map_restoreEdge,
        ih]

/-- Lowering an absent ambient edge preserves the number of residual darts. -/
theorem residualDarts_length_lowerTokensAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    (residualDarts
      (lowerTokensAvoiding a tokens ha)).length =
        (residualDarts tokens).length := by
  have hrestore :=
    residualEdges_lowerTokensAvoiding_map_restoreEdge
      a tokens ha
  have hlength := congrArg List.length hrestore
  simpa using hlength

/-- Re-embedding all protected edge names after lowering a marked word recovers the source
protected namespace exactly. -/
theorem protectedEdges_lowerTokensAvoiding_map_restoreEdge
    {n : ℕ} (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    (protectedEdges
      (lowerTokensAvoiding a tokens ha)).map
        (Cancellation.restoreEdge a) =
      protectedEdges tokens := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      rw [show
        lowerTokensAvoiding a (token :: tokens) ha =
          token.lowerAvoiding a (by
            intro htoken
            apply ha
            simp [htoken]) ::
          lowerTokensAvoiding a tokens (by
            intro htokens
            apply ha
            simp [htokens]) by rfl]
      simp only [protectedEdges_cons, List.map_append]
      rw [token.extractedEdges_lowerAvoiding_map_restoreEdge,
        ih]

/-- Re-embedding all distinct protected names after lowering recovers the source name spine. -/
theorem protectedNames_lowerTokensAvoiding_map_restoreEdge
    {n : ℕ} (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart) :
    (protectedNames
      (lowerTokensAvoiding a tokens ha)).map
        (Cancellation.restoreEdge a) =
      protectedNames tokens := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      rw [show
        lowerTokensAvoiding a (token :: tokens) ha =
          token.lowerAvoiding a (by
            intro htoken
            apply ha
            simp [htoken]) ::
          lowerTokensAvoiding a tokens (by
            intro htokens
            apply ha
            simp [htokens]) by rfl]
      simp only [protectedNames_cons, List.map_append]
      rw [token.extractedNames_lowerAvoiding_map_restoreEdge,
        ih]

/-- Injective cancellation lowering preserves separation of residual and protected names. -/
theorem IsSeparated.lowerTokensAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart)
    (separated : IsSeparated tokens) :
    IsSeparated (lowerTokensAvoiding a tokens ha) := by
  rw [IsSeparated, List.disjoint_left]
  intro e heResidual heProtected
  have hrestoredResidual :
      Cancellation.restoreEdge a e ∈
        (residualDarts tokens).map edgeOfDart := by
    rw [←
      residualEdges_lowerTokensAvoiding_map_restoreEdge
        a tokens ha]
    exact List.mem_map.mpr ⟨e, heResidual, rfl⟩
  have hrestoredProtected :
      Cancellation.restoreEdge a e ∈
        protectedEdges tokens := by
    rw [←
      protectedEdges_lowerTokensAvoiding_map_restoreEdge
        a tokens ha]
    exact List.mem_map.mpr ⟨e, heProtected, rfl⟩
  exact (List.disjoint_left.mp separated)
    hrestoredResidual hrestoredProtected

/-- An edge occurs in the expanded word exactly when it is residual or protected in an extracted
block token. -/
theorem mem_map_edgeOfDart_expand_iff {n : ℕ}
    (tokens : List (ReductionToken n)) (a : Fin n) :
    a ∈ (expand tokens).map edgeOfDart ↔
      a ∈ (residualDarts tokens).map edgeOfDart ∨
        a ∈ protectedEdges tokens := by
  induction tokens with
  | nil =>
      simp
  | cons token tokens ih =>
      cases token with
      | residual dart =>
          simp only [expand_cons, word_residual,
            residualDarts_cons, residualWord_residual,
            protectedEdges_cons, extractedEdges_residual,
            List.nil_append, List.map_append, List.map_cons,
            List.map_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false]
          rw [ih]
          tauto
      | extracted block =>
          simp only [expand_cons, word_extracted,
            residualDarts_cons, residualWord_extracted,
            protectedEdges_cons, extractedEdges_extracted,
            List.nil_append, List.map_append,
            List.mem_append]
          rw [ExtractedBlock.mem_map_edgeOfDart_word_iff,
            ih]
          tauto
      | completed block =>
          simp only [expand_cons, word_completed,
            residualDarts_cons, residualWord_completed,
            protectedEdges_cons, extractedEdges_completed,
            List.nil_append, List.map_append,
            List.mem_append]
          rw [CompletedBlock.mem_map_edgeOfDart_word_iff,
            ih]
          tauto

/-- A name absent from a token's protected part has the same multiplicity in its exact word and
its residual contribution. -/
theorem count_map_edgeOfDart_word_eq_residualWord_of_not_mem_extractedEdges
    {n : ℕ} (token : ReductionToken n) (a : Fin n)
    (ha : a ∉ token.extractedEdges) :
    (token.word.map edgeOfDart).count a =
      (token.residualWord.map edgeOfDart).count a := by
  cases token with
  | residual dart =>
      rfl
  | extracted block =>
      simp only [word_extracted, residualWord_extracted,
        List.map_nil, List.count_nil]
      apply List.count_eq_zero.mpr
      simpa only [ExtractedBlock.mem_map_edgeOfDart_word_iff,
        extractedEdges_extracted] using ha
  | completed block =>
      simp only [word_completed, residualWord_completed,
        List.map_nil, List.count_nil]
      apply List.count_eq_zero.mpr
      simpa only [CompletedBlock.mem_map_edgeOfDart_word_iff,
        extractedEdges_completed] using ha

/-- A name absent from every protected token has the same multiplicity in the expanded word and
the erased residual word. -/
theorem count_map_edgeOfDart_expand_eq_residualDarts_of_not_mem_protectedEdges
    {n : ℕ} (tokens : List (ReductionToken n)) (a : Fin n)
    (ha : a ∉ protectedEdges tokens) :
    ((expand tokens).map edgeOfDart).count a =
      ((residualDarts tokens).map edgeOfDart).count a := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      have htoken : a ∉ token.extractedEdges := by
        intro hmem
        exact ha (by simp [hmem])
      have htail : a ∉ protectedEdges tokens := by
        intro hmem
        exact ha (by simp [hmem])
      simp only [expand_cons, residualDarts_cons,
        List.map_append, List.count_append]
      rw [
        count_map_edgeOfDart_word_eq_residualWord_of_not_mem_extractedEdges
          token a htoken,
        ih htail]

/-- Flattening preserves a cyclic rotation of a list of lists. -/
theorem isRotated_flatten {α : Type*}
    {lists target : List (List α)}
    (hrotated : lists.IsRotated target) :
    lists.flatten.IsRotated target.flatten := by
  rcases hrotated with ⟨steps, hsteps⟩
  let cut := steps % lists.length
  let left := lists.take cut
  let right := lists.drop cut
  have hlists : lists = left ++ right :=
    (List.take_append_drop cut lists).symm
  have htarget : target = right ++ left := by
    rw [← hsteps, List.rotate_eq_drop_append_take_mod]
  rw [hlists, htarget, List.flatten_append,
    List.flatten_append]
  exact List.isRotated_append

/-- Expanding atomic marked tokens preserves cyclic rotation. -/
theorem expand_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (hrotated : tokens.IsRotated target) :
    (expand tokens).IsRotated (expand target) := by
  exact isRotated_flatten (hrotated.map word)

/-- Protected edge names rotate with their atomic marked tokens. -/
theorem protectedEdges_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (hrotated : tokens.IsRotated target) :
    (protectedEdges tokens).IsRotated
      (protectedEdges target) := by
  exact isRotated_flatten (hrotated.map extractedEdges)

/-- Distinct protected-name spines rotate with their atomic marked tokens. -/
theorem protectedNames_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (hrotated : tokens.IsRotated target) :
    (protectedNames tokens).IsRotated
      (protectedNames target) := by
  exact isRotated_flatten (hrotated.map extractedNames)

/-- Residual edge names rotate with their atomic marked tokens. -/
theorem residualEdges_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (hrotated : tokens.IsRotated target) :
    ((residualDarts tokens).map edgeOfDart).IsRotated
      ((residualDarts target).map edgeOfDart) := by
  exact (isRotated_flatten (hrotated.map residualWord)).map edgeOfDart

/-- Separation of residual and protected edge names is invariant under cyclic rotation. -/
theorem IsSeparated.of_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (separated : IsSeparated tokens)
    (hrotated : tokens.IsRotated target) :
    IsSeparated target := by
  rw [IsSeparated, List.disjoint_left]
  intro a haResidual haProtected
  exact
    (List.disjoint_left.mp separated)
      ((residualEdges_isRotated hrotated).perm.mem_iff.mpr
        haResidual)
      ((protectedEdges_isRotated hrotated).perm.mem_iff.mpr
        haProtected)

/-- Separation depends only on the multiset of atomic marked tokens. -/
theorem IsSeparated.of_perm {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (separated : IsSeparated tokens)
    (permuted : tokens.Perm target) :
    IsSeparated target := by
  have residualPerm :
      (residualDarts tokens).Perm
        (residualDarts target) := by
    simpa [residualDarts, List.flatMap] using
      (List.Perm.flatMap permuted
        (f := residualWord) (g := residualWord)
        (fun _ _ => List.Perm.refl _))
  have protectedPerm :
      (protectedEdges tokens).Perm
        (protectedEdges target) := by
    simpa [protectedEdges, List.flatMap] using
      (List.Perm.flatMap permuted
        (f := extractedEdges) (g := extractedEdges)
        (fun _ _ => List.Perm.refl _))
  rw [IsSeparated, List.disjoint_left]
  intro edge hResidual hProtected
  exact (List.disjoint_left.mp separated)
    ((residualPerm.map edgeOfDart).mem_iff.mpr hResidual)
    (protectedPerm.mem_iff.mpr hProtected)

/-- Permuting atomic marked tokens permutes their distinct protected-name spines. -/
theorem protectedNames_perm {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (permuted : tokens.Perm target) :
    (protectedNames tokens).Perm
      (protectedNames target) := by
  simpa [protectedNames, List.flatMap] using
    (List.Perm.flatMap permuted
      (f := extractedNames) (g := extractedNames)
      (fun _ _ => List.Perm.refl _))

/-- Duplicate-freeness of protected names depends only on the multiset of marked tokens. -/
theorem protectedNames_nodup_of_perm {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (nodup : (protectedNames tokens).Nodup)
    (permuted : tokens.Perm target) :
    (protectedNames target).Nodup :=
  (protectedNames_perm permuted).nodup_iff.mp nodup

/-- Permuting marked tokens preserves nonemptiness of the protected-name spine. -/
theorem protectedNames_ne_nil_of_perm {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (hne : protectedNames tokens ≠ [])
    (permuted : tokens.Perm target) :
    protectedNames target ≠ [] := by
  intro htarget
  apply hne
  have hlength :=
    (protectedNames_perm permuted).length_eq
  apply List.length_eq_zero_iff.mp
  rw [hlength, htarget]
  rfl

/-- Permuting atomic marked tokens preserves the number of residual darts. -/
theorem residualDarts_length_of_perm {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (permuted : tokens.Perm target) :
    (residualDarts target).length =
      (residualDarts tokens).length := by
  have hperm :
      (residualDarts tokens).Perm
        (residualDarts target) := by
    simpa [residualDarts, List.flatMap] using
      (List.Perm.flatMap permuted
        (f := residualWord) (g := residualWord)
        (fun _ _ => List.Perm.refl _))
  exact hperm.length_eq.symm

/-- Lowering an absent ambient edge preserves duplicate-freeness of all protected names. -/
theorem protectedNames_nodup_lowerTokensAvoiding {n : ℕ}
    (a : Fin (n + 1))
    (tokens : List (ReductionToken (n + 1)))
    (ha : a ∉ (expand tokens).map edgeOfDart)
    (nodup : (protectedNames tokens).Nodup) :
    (protectedNames
      (lowerTokensAvoiding a tokens ha)).Nodup := by
  have mappedNodup :
      ((protectedNames
        (lowerTokensAvoiding a tokens ha)).map
          (Cancellation.restoreEdge a)).Nodup := by
    rw [protectedNames_lowerTokensAvoiding_map_restoreEdge]
    exact nodup
  exact mappedNodup.of_map _

/-- A separated marked word cannot protect an edge that still occurs residually. -/
theorem IsSeparated.not_mem_protected_of_mem_residual {n : ℕ}
    {tokens : List (ReductionToken n)}
    (separated : IsSeparated tokens) (a : Fin n)
    (ha : a ∈ (residualDarts tokens).map edgeOfDart) :
    a ∉ protectedEdges tokens := by
  intro haProtected
  exact (List.disjoint_left.mp separated) ha haProtected

@[simp]
theorem expand_ofWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    expand (ofWord word) = word := by
  induction word with
  | nil =>
      rfl
  | cons dart word ih =>
      change
        expand (.residual dart :: ofWord word) =
          dart :: word
      rw [expand_cons, word_residual, ih]
      rfl

@[simp]
theorem residualDarts_ofWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    residualDarts (ofWord word) = word := by
  induction word with
  | nil =>
      rfl
  | cons dart word ih =>
      change
        residualDarts (.residual dart :: ofWord word) =
          dart :: word
      rw [residualDarts_cons, residualWord_residual, ih]
      rfl

@[simp]
theorem protectedEdges_ofWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    protectedEdges (ofWord word) = [] := by
  induction word with
  | nil =>
      rfl
  | cons dart word ih =>
      change
        protectedEdges (.residual dart :: ofWord word) = []
      simp [ih]

@[simp]
theorem protectedNames_ofWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    protectedNames (ofWord word) = [] := by
  induction word with
  | nil =>
      rfl
  | cons dart word ih =>
      change
        protectedNames (.residual dart :: ofWord word) = []
      simp [ih]

@[simp]
theorem expand_ofBlocks {n : ℕ}
    (blocks : List (ExtractedBlock n)) :
    expand (ofBlocks blocks) =
      ExtractedBlock.sequenceWord blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      change
        expand (.extracted block :: ofBlocks blocks) =
          ExtractedBlock.sequenceWord (block :: blocks)
      rw [expand_cons, word_extracted, ih,
        ExtractedBlock.sequenceWord_cons]

@[simp]
theorem residualDarts_ofBlocks {n : ℕ}
    (blocks : List (ExtractedBlock n)) :
    residualDarts (ofBlocks blocks) = [] := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      change
        residualDarts (.extracted block :: ofBlocks blocks) = []
      rw [residualDarts_cons, residualWord_extracted, ih,
        List.nil_append]

/-- Lift a displayed residual dart occurrence to an exact split of the marked token list. -/
theorem exists_split_of_residualDarts_eq_append_cons {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (dart : SignedDart (Fin n))
    (hresidual :
      residualDarts tokens = left ++ dart :: right) :
    ∃ tokenLeft tokenRight,
      tokens = tokenLeft ++ .residual dart :: tokenRight ∧
        residualDarts tokenLeft = left ∧
        residualDarts tokenRight = right := by
  induction tokens generalizing left with
  | nil =>
      simp at hresidual
  | cons token tokens ih =>
      cases token with
      | extracted block =>
          simp only [residualDarts_cons, residualWord,
            List.nil_append] at hresidual
          rcases ih left hresidual with
            ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
          exact
            ⟨.extracted block :: tokenLeft, tokenRight,
              by simp [htokens],
              by
                simp only [residualDarts_cons, residualWord,
                  List.nil_append]
                exact hleft,
              hright⟩
      | completed block =>
          simp only [residualDarts_cons,
            residualWord_completed,
            List.nil_append] at hresidual
          rcases ih left hresidual with
            ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
          exact
            ⟨.completed block :: tokenLeft, tokenRight,
              by simp [htokens],
              by
                simp only [residualDarts_cons,
                  residualWord_completed,
                  List.nil_append]
                exact hleft,
              hright⟩
      | residual first =>
          cases left with
          | nil =>
              simp only [residualDarts_cons, residualWord,
                List.singleton_append, List.nil_append,
                List.cons.injEq] at hresidual
              rcases hresidual with ⟨rfl, htail⟩
              exact ⟨[], tokens, rfl, rfl, htail⟩
          | cons head left =>
              simp only [residualDarts_cons, residualWord,
                List.cons_append, List.cons.injEq,
                List.nil_append] at hresidual
              rcases hresidual with ⟨rfl, htail⟩
              rcases ih left htail with
                ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
              exact
                ⟨.residual first :: tokenLeft, tokenRight,
                  by simp [htokens], by simp [hleft], hright⟩

/-- Lift an arbitrary residual-word cut to a cut of the marked token list. -/
theorem exists_split_of_residualDarts_eq_append {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (hresidual : residualDarts tokens = left ++ right) :
    ∃ tokenLeft tokenRight,
      tokens = tokenLeft ++ tokenRight ∧
        residualDarts tokenLeft = left ∧
        residualDarts tokenRight = right := by
  induction tokens generalizing left with
  | nil =>
      have happend : left ++ right = [] := hresidual.symm
      have hparts : left = [] ∧ right = [] := by
        simpa using happend
      rcases hparts with ⟨hleft, hright⟩
      subst left
      subst right
      exact ⟨[], [], rfl, rfl, rfl⟩
  | cons token tokens ih =>
      cases token with
      | extracted block =>
          simp only [residualDarts_cons,
            residualWord_extracted, List.nil_append] at hresidual
          rcases ih left hresidual with
            ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
          exact
            ⟨.extracted block :: tokenLeft, tokenRight,
              by simp [htokens],
              by
                simp only [residualDarts_cons,
                  residualWord_extracted, List.nil_append]
                exact hleft,
              hright⟩
      | completed block =>
          simp only [residualDarts_cons,
            residualWord_completed,
            List.nil_append] at hresidual
          rcases ih left hresidual with
            ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
          exact
            ⟨.completed block :: tokenLeft, tokenRight,
              by simp [htokens],
              by
                simp only [residualDarts_cons,
                  residualWord_completed,
                  List.nil_append]
                exact hleft,
              hright⟩
      | residual first =>
          cases left with
          | nil =>
              exact
                ⟨[], .residual first :: tokens, rfl, rfl,
                  by simpa using hresidual⟩
          | cons head left =>
              simp only [residualDarts_cons,
                residualWord_residual,
                List.cons_append, List.cons.injEq] at hresidual
              rcases hresidual with ⟨rfl, htail⟩
              rcases ih left htail with
                ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
              exact
                ⟨.residual first :: tokenLeft, tokenRight,
                  by simp [htokens],
                  by simp [hleft],
                  hright⟩

/-- Every cyclic rotation of the residual darts is induced by a cyclic rotation of the marked
tokens. -/
theorem exists_isRotated_of_residualDarts_isRotated {n : ℕ}
    (tokens : List (ReductionToken n))
    {target : List (SignedDart (Fin n))}
    (hrotated : (residualDarts tokens).IsRotated target) :
    ∃ rotatedTokens,
      tokens.IsRotated rotatedTokens ∧
        residualDarts rotatedTokens = target := by
  rcases hrotated with ⟨steps, hsteps⟩
  let cut := steps % (residualDarts tokens).length
  let left := (residualDarts tokens).take cut
  let right := (residualDarts tokens).drop cut
  have hsource :
      residualDarts tokens = left ++ right := by
    exact (List.take_append_drop cut
      (residualDarts tokens)).symm
  have htarget :
      target = right ++ left := by
    rw [← hsteps, List.rotate_eq_drop_append_take_mod]
  rcases exists_split_of_residualDarts_eq_append
      tokens left right hsource with
    ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
  refine ⟨tokenRight ++ tokenLeft, ?_, ?_⟩
  · rw [htokens]
    exact List.isRotated_append
  · rw [residualDarts_append, hright, hleft, ← htarget]

/-- Lift a residual rotation which displays one dart at its head to a marked-token rotation with
that exact residual token at its head. -/
theorem exists_isRotated_residual_cons {n : ℕ}
    (tokens : List (ReductionToken n))
    (dart : SignedDart (Fin n))
    (remainder : List (SignedDart (Fin n)))
    (hrotated :
      (residualDarts tokens).IsRotated (dart :: remainder)) :
    ∃ tokenRemainder,
      tokens.IsRotated
        (.residual dart :: tokenRemainder) ∧
      residualDarts tokenRemainder = remainder := by
  rcases exists_isRotated_of_residualDarts_isRotated
      tokens hrotated with
    ⟨rotatedTokens, htokens, hresidual⟩
  have hdisplay :
      residualDarts rotatedTokens =
        [] ++ dart :: remainder := by
    simpa using hresidual
  rcases exists_split_of_residualDarts_eq_append_cons
      rotatedTokens [] remainder dart hdisplay with
    ⟨tokenLeft, tokenRight, hsplit, hleft, hright⟩
  refine ⟨tokenRight ++ tokenLeft, ?_, ?_⟩
  · apply htokens.trans
    rw [hsplit]
    simpa only [List.nil_append, List.cons_append] using
      (List.isRotated_append
        (l := tokenLeft)
        (l' := .residual dart :: tokenRight))
  · rw [residualDarts_append, hright, hleft]
    simp

/-- Type-valued packaging of a marked split, suitable for recursive normalization data. -/
structure ResidualSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n))) where
  /-- The `tokenLeft` declaration. -/
  tokenLeft : List (ReductionToken n)
  /-- The `tokenRight` declaration. -/
  tokenRight : List (ReductionToken n)
  tokens_eq : tokens = tokenLeft ++ tokenRight
  residual_left : residualDarts tokenLeft = left
  residual_right : residualDarts tokenRight = right

/-- Type-valued packaging of a marked split at one displayed residual dart. -/
structure ResidualDartSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (dart : SignedDart (Fin n)) where
  /-- The `tokenLeft` declaration. -/
  tokenLeft : List (ReductionToken n)
  /-- The `tokenRight` declaration. -/
  tokenRight : List (ReductionToken n)
  tokens_eq :
    tokens = tokenLeft ++ .residual dart :: tokenRight
  residual_left : residualDarts tokenLeft = left
  residual_right : residualDarts tokenRight = right

/-- Choose a marked split above a displayed residual-word split. -/
noncomputable def residualSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (hresidual : residualDarts tokens = left ++ right) :
    ResidualSplit tokens left right := by
  let witness :=
    exists_split_of_residualDarts_eq_append
      tokens left right hresidual
  let tokenLeft := Classical.choose witness
  let rightWitness := Classical.choose_spec witness
  let tokenRight := Classical.choose rightWitness
  let properties := Classical.choose_spec rightWitness
  exact
    { tokenLeft := tokenLeft
      tokenRight := tokenRight
      tokens_eq := properties.1
      residual_left := properties.2.1
      residual_right := properties.2.2 }

/-- Choose a marked split at a displayed residual dart. -/
noncomputable def residualDartSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (dart : SignedDart (Fin n))
    (hresidual :
      residualDarts tokens = left ++ dart :: right) :
    ResidualDartSplit tokens left right dart := by
  let witness :=
    exists_split_of_residualDarts_eq_append_cons
      tokens left right dart hresidual
  let tokenLeft := Classical.choose witness
  let rightWitness := Classical.choose_spec witness
  let tokenRight := Classical.choose rightWitness
  let properties := Classical.choose_spec rightWitness
  exact
    { tokenLeft := tokenLeft
      tokenRight := tokenRight
      tokens_eq := properties.1
      residual_left := properties.2.1
      residual_right := properties.2.2 }

/-- Type-valued packaging of a marked rotation with one residual dart at its head. -/
structure ResidualConsRotation {n : ℕ}
    (tokens : List (ReductionToken n))
    (dart : SignedDart (Fin n))
    (remainder : List (SignedDart (Fin n))) where
  /-- The `tokenRemainder` declaration. -/
  tokenRemainder : List (ReductionToken n)
  rotated :
    tokens.IsRotated (.residual dart :: tokenRemainder)
  residual_remainder :
    residualDarts tokenRemainder = remainder

/-- Choose the marked rotation above a residual rotation with one displayed head dart. -/
noncomputable def residualConsRotation {n : ℕ}
    (tokens : List (ReductionToken n))
    (dart : SignedDart (Fin n))
    (remainder : List (SignedDart (Fin n)))
    (hrotated :
      (residualDarts tokens).IsRotated (dart :: remainder)) :
    ResidualConsRotation tokens dart remainder := by
  let witness :=
    exists_isRotated_residual_cons
      tokens dart remainder hrotated
  let tokenRemainder := Classical.choose witness
  let properties := Classical.choose_spec witness
  exact
    { tokenRemainder := tokenRemainder
      rotated := properties.1
      residual_remainder := properties.2 }

@[simp]
theorem expand_inverseSequence {n : ℕ}
    (tokens : List (ReductionToken n)) :
    expand (inverseSequence tokens) =
      inverseWord (expand tokens) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      have ih' :
          expand ((tokens.map inverse).reverse) =
            inverseWord (expand tokens) := by
        simpa only [inverseSequence] using ih
      simp [inverseSequence, inverseWord_append, ih']

@[simp]
theorem residualDarts_inverseSequence {n : ℕ}
    (tokens : List (ReductionToken n)) :
    residualDarts (inverseSequence tokens) =
      inverseWord (residualDarts tokens) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      have ih' :
          residualDarts ((tokens.map inverse).reverse) =
            inverseWord (residualDarts tokens) := by
        simpa only [inverseSequence] using ih
      simp [inverseSequence, inverseWord_append, ih']

@[simp]
theorem protectedEdges_inverseSequence {n : ℕ}
    (tokens : List (ReductionToken n)) :
    protectedEdges (inverseSequence tokens) =
      (protectedEdges tokens).reverse := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      have ih' :
          protectedEdges ((tokens.map inverse).reverse) =
            (protectedEdges tokens).reverse := by
        simpa only [inverseSequence] using ih
      simp [inverseSequence, ih', List.reverse_append]

/-- Reversing a marked token sequence preserves its multiset of distinct protected names. -/
theorem protectedNames_inverseSequence_perm {n : ℕ}
    (tokens : List (ReductionToken n)) :
    (protectedNames (inverseSequence tokens)).Perm
      (protectedNames tokens) := by
  induction tokens with
  | nil =>
      exact List.Perm.refl []
  | cons token tokens ih =>
      have hcombined :
          (protectedNames (inverseSequence tokens) ++
              token.inverse.extractedNames).Perm
            (protectedNames tokens ++
              token.extractedNames) :=
        List.Perm.append ih token.extractedNames_inverse_perm
      have hreordered :
          (protectedNames tokens ++
              token.extractedNames).Perm
            (token.extractedNames ++
              protectedNames tokens) :=
        List.perm_append_comm
      simpa [inverseSequence, protectedNames,
        List.flatMap] using hcombined.trans hreordered

@[simp]
theorem expand_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (tokens : List (ReductionToken n)) :
    expand (tokens.map (mapEquiv e)) =
      (expand tokens).map (SignedDart.mapEquiv e) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      simp [ih]

@[simp]
theorem residualDarts_mapEquiv {n m : ℕ}
    (e : Fin n ≃ Fin m)
    (tokens : List (ReductionToken n)) :
    residualDarts (tokens.map (mapEquiv e)) =
      (residualDarts tokens).map (SignedDart.mapEquiv e) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      simp [ih]

end ReductionToken

end Pairing

end WordReduction

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
