/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP1
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2
import LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization

/-!
# Finite cyclic move closures

This file combines signed presentation isomorphisms and the two primitive Gallier--Xu
subdivisions into stable closure APIs.

`Subdivides` is the directed reflexive-transitive closure. It preserves ordinary validity,
connectivity, and Gallier validity. `HasCommonSubdivision P Q` supplies a validity-safe common
target for topological comparison: starting with two ordinary-valid presentations, both forward
chains remain ordinary-valid. This is stronger operational data than an unrestricted symmetric
move chain, which may pass through the exceptional empty-word sphere where
`PolygonalRealization` is deliberately unavailable.

`MoveEquivalent` is also provided as the purely syntactic equivalence closure. A common
subdivision implies move equivalence, but no converse or confluence theorem is asserted here.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

/-- One directed presentation step: a signed isomorphism, P1 subdivision, or P2 subdivision. -/
def SubdivisionStep (P Q : FiniteCyclicPresentation) : Prop :=
  Nonempty (SignedPresentationIso P Q) ∨
    P1Subdivision P Q ∨ P2Subdivision P Q

namespace SubdivisionStep

theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) :
    SubdivisionStep P Q :=
  Or.inl ⟨e⟩

theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inl h)

theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inr h)

/-- Every directed step preserves ordinary surface incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isSurfaceValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isSurfaceValid validP
    · exact hP2.isSurfaceValid validP

/-- Every directed step preserves face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isConnected connectedP
  · rcases hrest with hP1 | hP2
    · exact hP1.isConnected connectedP
    · exact hP2.isConnected connectedP

/-- Every directed step preserves the packed Gallier--Xu validity predicate. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isGallierValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isGallierValid validP
    · exact hP2.isGallierValid validP

end SubdivisionStep

/-- Directed finite subdivision by signed isomorphisms, P1, and P2. -/
def Subdivides (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.ReflTransGen SubdivisionStep P Q

namespace Subdivides

theorem refl (P : FiniteCyclicPresentation) : Subdivides P P :=
  Relation.ReflTransGen.refl

theorem single {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : Subdivides P Q :=
  Relation.ReflTransGen.single h

theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : Subdivides P Q :=
  single (SubdivisionStep.signedIso e)

theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p1 h)

theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p2 h)

theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (hQR : Subdivides Q R) :
    Subdivides P R :=
  Relation.ReflTransGen.trans hPQ hQR

/-- Directed subdivision chains preserve ordinary surface incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isSurfaceValid ih

/-- Directed subdivision chains preserve face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  induction hPQ with
  | refl =>
      exact connectedP
  | tail _ hstep ih =>
      exact hstep.isConnected ih

/-- Directed subdivision chains preserve Gallier validity. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isGallierValid ih

end Subdivides

/-- Two presentations have a common directed subdivision. -/
def HasCommonSubdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ R : FiniteCyclicPresentation, Subdivides P R ∧ Subdivides Q R

namespace HasCommonSubdivision

theorem refl (P : FiniteCyclicPresentation) : HasCommonSubdivision P P :=
  ⟨P, Subdivides.refl P, Subdivides.refl P⟩

theorem symm {P Q : FiniteCyclicPresentation}
    (h : HasCommonSubdivision P Q) :
    HasCommonSubdivision Q P := by
  rcases h with ⟨R, hPR, hQR⟩
  exact ⟨R, hQR, hPR⟩

end HasCommonSubdivision

/-- Purely syntactic equivalence generated by signed isomorphisms, P1, and P2. -/
def MoveEquivalent (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.EqvGen SubdivisionStep P Q

namespace MoveEquivalent

theorem refl (P : FiniteCyclicPresentation) : MoveEquivalent P P :=
  Relation.EqvGen.refl P

theorem ofStep {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : MoveEquivalent P Q :=
  Relation.EqvGen.rel P Q h

theorem symm {P Q : FiniteCyclicPresentation}
    (h : MoveEquivalent P Q) : MoveEquivalent Q P :=
  Relation.EqvGen.symm P Q h

theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : MoveEquivalent P Q) (hQR : MoveEquivalent Q R) :
    MoveEquivalent P R :=
  Relation.EqvGen.trans P Q R hPQ hQR

end MoveEquivalent

/-- Every directed subdivision chain is a syntactic move equivalence. -/
theorem Subdivides.moveEquivalent {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) :
    MoveEquivalent P Q := by
  induction hPQ with
  | refl =>
      exact MoveEquivalent.refl P
  | @tail Q R _ hstep ih =>
      exact ih.trans (MoveEquivalent.ofStep hstep)

/-- A common directed subdivision is in particular a syntactic move equivalence. -/
theorem HasCommonSubdivision.moveEquivalent
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q) :
    MoveEquivalent P Q := by
  rcases h with ⟨R, hPR, hQR⟩
  exact hPR.moveEquivalent.trans hQR.moveEquivalent.symm

namespace PolygonallyEquivalent

theorem refl (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent P validP validP :=
  ⟨Homeomorph.refl _⟩

theorem symm {P Q : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    (h : P.PolygonallyEquivalent Q validP validQ) :
    Q.PolygonallyEquivalent P validQ validP := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem trans {P Q R : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    {validR : R.IsSurfaceValid}
    (hPQ : P.PolygonallyEquivalent Q validP validQ)
    (hQR : Q.PolygonallyEquivalent R validQ validR) :
    P.PolygonallyEquivalent R validP validR := by
  rcases hPQ with ⟨ePQ⟩
  rcases hQR with ⟨eQR⟩
  exact ⟨ePQ.trans eQR⟩

end PolygonallyEquivalent

/-- The stable proof obligation for primitive realization invariance.

The P1 and P2 realization files discharge the corresponding disjuncts; signed isomorphisms are
already implemented by `SignedPresentationIso.polygonallyEquivalent`. -/
def SubdivisionStep.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, SubdivisionStep P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- The realization-invariance obligation isolated to P1 subdivisions. -/
def P1Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P1Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- The realization-invariance obligation isolated to P2 subdivisions. -/
def P2Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P2Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- Signed-isomorphism invariance plus the two primitive geometric obligations supplies invariance
for every directed elementary step. -/
theorem SubdivisionStep.preservesPolygonalRealization
    (hP1 : P1Subdivision.PreservesPolygonalRealization)
    (hP2 : P2Subdivision.PreservesPolygonalRealization) :
    SubdivisionStep.PreservesPolygonalRealization := by
  intro P Q hstep validP validQ
  rcases hstep with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.polygonallyEquivalent validP validQ
  · rcases hrest with hP1Step | hP2Step
    · exact hP1 hP1Step validP validQ
    · exact hP2 hP2Step validP validQ

/-- If every primitive directed step preserves the faithful polygonal quotient, so does every
directed subdivision chain. -/
theorem Subdivides.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  induction hPQ with
  | refl =>
      exact PolygonallyEquivalent.refl P validP
  | @tail R Q hPR hstep ih =>
      let validR : R.IsSurfaceValid :=
        Subdivides.isSurfaceValid hPR validP
      exact (ih validR).trans (hprimitive hstep validR validQ)

/-- Primitive realization invariance promotes a common-subdivision certificate to a
homeomorphism of faithful polygonal quotients. -/
theorem HasCommonSubdivision.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  rcases h with ⟨R, hPR, hQR⟩
  let validR : R.IsSurfaceValid :=
    Subdivides.isSurfaceValid hPR validP
  exact
    (hPR.polygonallyEquivalent hprimitive validP validR).trans
      (hQR.polygonallyEquivalent hprimitive validQ validR).symm

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
