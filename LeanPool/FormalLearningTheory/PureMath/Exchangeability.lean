/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Exchangeability and Double-Sample Infrastructure

Pure mathematical infrastructure for double-sample constructions, merged samples,
valid splits, and split measures. No learning-theory types.

## Main definitions

- `ExchangeableSample` : bundles sample size m, measure μ, and probability measure proof
- `DoubleSampleMeasure` : D^m ⊗ D^m as product of two independent pi measures
- `MergedSample` : Fin (2*m) → X type alias
- `mergeSamples` / `splitMergedSample` : merge/split isomorphism
- `ValidSplit` : assignment of 2m indices to two groups of m
- `SplitMeasure` : uniform measure over valid splits
- `splitFirst` / `splitSecond` : extract groups from a merged sample

## References

- Shalev-Shwartz & Ben-David, "Understanding Machine Learning", Chapter 4 / 6
- Kakade & Tewari, Lecture 19: Symmetrization
-/

universe u

open MeasureTheory ENNReal

/-- Bundle for an exchangeable sample: sample size, measure, and probability measure proof. -/
structure ExchangeableSample {X : Type*} [MeasurableSpace X] where
  m : ℕ
  μ : MeasureTheory.Measure X
  hμ : MeasureTheory.IsProbabilityMeasure μ

/-- The double sample measure: D^m ⊗ D^m, the product of two independent
    m-fold product measures. This is the joint distribution of the training
    sample S and the ghost sample S'.

    Construction: `Measure.pi` gives D^m on `Fin m → X`. The `.prod` gives
    the product of two such measures on `(Fin m → X) × (Fin m → X)`.

    Measurability: both factors are probability measures (by `Measure.pi`
    preserving `IsProbabilityMeasure`), so the product is also a probability measure. -/
noncomputable def DoubleSampleMeasure {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (m : ℕ) : MeasureTheory.Measure ((Fin m → X) × (Fin m → X)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
    (MeasureTheory.Measure.pi (fun _ : Fin m => D))

/-- Type alias for a merged sample of 2m points from X.
    A merged sample arises from concatenating the training sample S and ghost sample S'
    into a single sequence of 2m points. The key property is that under D^{2m},
    all 2m points are iid, so the joint distribution is invariant under permutations. -/
abbrev MergedSample (X : Type u) (m : ℕ) := Fin (2 * m) → X

/-- Merge two samples of size m into a single sample of size 2m.
    Uses `Fin.append` via the canonical `Fin m ⊕ Fin m ≃ Fin (m + m)` isomorphism,
    composed with the `m + m = 2 * m` cast.

    This is the structural bridge between `(Fin m → X) × (Fin m → X)` and
    `Fin (2*m) → X`. The inverse is `splitMergedSample`. -/
noncomputable def mergeSamples {X : Type u} {m : ℕ}
    (p : (Fin m → X) × (Fin m → X)) : MergedSample X m :=
  fun i =>
    let j : Fin (m + m) := i.cast (two_mul m)
    if h : j.val < m
    then p.1 ⟨j.val, h⟩
    else p.2 ⟨j.val - m, by omega⟩

/-- Split a merged sample of 2m points back into two samples of size m.
    Inverse of `mergeSamples`. -/
noncomputable def splitMergedSample {X : Type u} {m : ℕ}
    (z : MergedSample X m) : (Fin m → X) × (Fin m → X) :=
  (fun i => z (Fin.castAdd m i |>.cast (two_mul m).symm),
   fun i => z (Fin.natAdd m i |>.cast (two_mul m).symm))

/-- A split of a 2m-element set into two groups of m.
    Represented as a function `Fin (2*m) → Bool` where `true` = first group, `false` = second.
    A valid split has exactly m elements in each group.

    The set of all valid splits has cardinality `Nat.choose (2*m) m`. -/
structure ValidSplit (m : ℕ) where
  /-- Assignment of each of 2m indices to one of two groups -/
  assign : Fin (2 * m) → Bool
  /-- Exactly m indices are assigned to the first group -/
  card_true : (Finset.univ.filter (fun i => assign i = true)).card = m
  deriving DecidableEq

/-- ValidSplit m is finite: it is a subtype of the finite type `Fin (2*m) → Bool`. -/
noncomputable instance (m : ℕ) : Fintype (ValidSplit m) :=
  Fintype.ofInjective (fun vs => vs.assign)
    (fun a b h => by cases a; cases b; simp_all)

/-- Discrete measurable space on ValidSplit (all sets measurable). -/
instance (m : ℕ) : MeasurableSpace (ValidSplit m) := ⊤

/-- The uniform measure over all valid splits of 2m elements into two groups of m.
    This is the key construction for the exchangeability argument (Approach A).

    Under D^{2m}, conditioning on the merged sample z and averaging over all
    valid splits gives the same distribution as D^m ⊗ D^m. This is because
    D^{2m} is invariant under permutations of coordinates.

    The measure assigns weight 1/C(2m,m) to each valid split.

    MEASURABILITY NOTE: ValidSplit m is a finite type (subtype of Fin (2*m) → Bool),
    so all sets are measurable under the discrete σ-algebra. -/
noncomputable def SplitMeasure (m : ℕ) : MeasureTheory.Measure (ValidSplit m) :=
  if _h : Fintype.card (ValidSplit m) = 0 then 0
  else (Fintype.card (ValidSplit m) : ENNReal)⁻¹ •
    ∑ vs : ValidSplit m, MeasureTheory.Measure.dirac vs

/-- Given a merged sample z and a valid split, extract the first group (training sample). -/
def splitFirst {X : Type u} {m : ℕ} (z : MergedSample X m) (_vs : ValidSplit m) :
    Fin m → X := by
  -- The first group consists of the m indices where assign = true
  -- We need to enumerate them and index into z
  exact fun i => z (Fin.castAdd m i |>.cast (two_mul m).symm)

/-- Given a merged sample z and a valid split, extract the second group (ghost sample). -/
def splitSecond {X : Type u} {m : ℕ} (z : MergedSample X m) (_vs : ValidSplit m) :
    Fin m → X := by
  exact fun i => z (Fin.natAdd m i |>.cast (two_mul m).symm)

attribute [nolint docBlame]
  ExchangeableSample.m
  ExchangeableSample.μ

attribute [nolint unusedArguments]
  splitFirst
  splitSecond
