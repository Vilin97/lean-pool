/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132N14.RegularTridecagon

/-!
# Published inputs for the conditional fourteen-point theorem

Exactly three external interfaces are used. They record the Hopf--Pannwitz
low-multiplicity diameter consequence at fourteen points, the published
cardinality bound for planar sets with at most six distances, and the
Szöllősi--Östergård classification of thirteen-point six-distance sets.

The cardinality interface packages the known planar maxima through six
distances. Its exact six-distance case is Wei's theorem `g(6) = 13`; the
smaller cases and their sources are summarized in Table 1 of the
Szöllősi--Östergård paper. The classification interface is Theorem 16 of that
paper and returns only a genuine Euclidean distance-scaling similarity to one
of the three explicit coordinate templates.
-/

namespace LeanPool.Erdos132N14

noncomputable section

/-- The three outcomes of the published maximum six-distance classification. -/
inductive ThirteenPointSixDistanceClassification
    {ι : Type} [LinearOrder ι] (P : Configuration ι) (S : Finset ι) : Prop
  | regular13 : SimilarTo P S regularTridecagon.point →
      ThirteenPointSixDistanceClassification P S
  | dodecagonWithCenter : SimilarTo P S dodecagonWithCenter.point →
      ThirteenPointSixDistanceClassification P S
  | hexagramWithCenter : SimilarTo P S hexagramWithCenter.point →
      ThirteenPointSixDistanceClassification P S

/-- Published Hopf--Pannwitz input: every fourteen-point planar set has a
realized distance represented by at most fourteen pairs. The published witness
is the diameter. -/
def HopfPannwitzLowMultiplicityDistance14 : Prop :=
  ∀ P : Configuration (Fin 14),
    ∃ d ∈ P.realizedDistances Finset.univ,
      P.distanceMultiplicity Finset.univ d ≤ 14

/-- Published planar few-distance input: a set determining at most six
distances has at most thirteen points. This combines the known maxima through
five distances with Wei's exact six-distance theorem `g(6) = 13`. -/
def PublishedAtMostSixDistanceCardinalityBound : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι]
    (P : Configuration ι) (S : Finset ι),
    (P.realizedDistances S).card ≤ 6 → S.card ≤ 13

/-- Published Szöllősi--Östergård input: every thirteen-point planar
six-distance set is similar to one of the three explicit templates. -/
def SzollosiOstergardThirteenPointSixDistanceClassification : Prop :=
  ∀ {ι : Type} [Fintype ι] [LinearOrder ι]
    (P : Configuration ι) (S : Finset ι),
    S.card = 13 → (P.realizedDistances S).card = 6 →
      ThirteenPointSixDistanceClassification P S

end

end LeanPool.Erdos132N14
