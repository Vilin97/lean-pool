/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions
import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Laws
import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SliceMeasurability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Restriction Law -/

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Chapter 4 restriction-engineering law assumptions (carrier re-type, Packet P3)

This file owns the separate pointwise-restriction/sup-metric engineering
assumptions used by the restriction lane of Chapter 4 and later chapters.
Following the carrier redesign, the single restriction-lane law carrier
`RestrictionCoeffLaw d` is a
measure on the honest-fields carrier `RegCoeffField d` (see
`Homogenization.Probability.RegCoeffField`), on which entrywise regularity is
free by type.  The structural predicates re-base onto the carrier endomorphisms
of `RegCoeffField/Laws.lean`; the ellipticity/slice predicates apply the raw
`IsAEEllipticFieldOn`/`AEEQuantitativeEllipticSlice` vocabulary to the honest
sample `a.toFun` (least-churn encoding: the a.e.-strong-measurability conjunct is
kept in the predicate but is always satisfiable on a carrier element, and the
downstream `L²` slice machinery still consumes it).

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

/-- Combine finitely many almost-everywhere statements into one statement over
all members of a finset. -/
theorem ae_forall_mem_finset {α ι : Type*} [MeasurableSpace α]
    {P : Measure α} (s : Finset ι) {p : ι → α → Prop}
    (h : ∀ i, i ∈ s → ∀ᵐ a ∂P, p i a) :
    ∀ᵐ a ∂P, ∀ i, i ∈ s → p i a := by
  classical
  revert h
  refine Finset.induction_on s ?empty ?insert
  · intro h
    exact Filter.Eventually.of_forall (by simp)
  · intro i s his ih h
    have hi : ∀ᵐ a ∂P, p i a := h i (by simp)
    have hs : ∀ᵐ a ∂P, ∀ j, j ∈ s → p j a := by
      exact ih fun j hj => h j (by simp [hj])
    filter_upwards [hi, hs] with a ha_i ha_s j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact ha_i
    · exact ha_s j hj

/-- Nested finite version of `ae_forall_mem_finset`. -/
theorem ae_forall_mem_finset_nested {α ι κ : Type*} [MeasurableSpace α]
    {P : Measure α} (s : Finset ι) (t : ι → Finset κ)
    {p : ι → κ → α → Prop}
    (h : ∀ i, i ∈ s → ∀ j, j ∈ t i → ∀ᵐ a ∂P, p i j a) :
    ∀ᵐ a ∂P, ∀ i, i ∈ s → ∀ j, j ∈ t i → p i j a :=
  ae_forall_mem_finset (P := P) s fun i hi =>
    ae_forall_mem_finset (P := P) (t i) fun j hj =>
      h i hi j hj

/-- A Chapter 4 law on global coefficient fields, carried by the honest-fields
carrier `RegCoeffField d` (regularity free by type). -/
abbrev RestrictionCoeffLaw (d : ℕ) :=
  Measure (RegCoeffField d)

/-- The measurable restriction-local coefficient-field sigma algebra on a
measurable observation set (carrier version). -/
noncomputable abbrev restrictionSigma {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurableSpace (RegCoeffField d) :=
  Homogenization.RestrictionSigmaR U hU

/-- Spatial a.e. ellipticity of a carrier coefficient field on an observation
set, evaluated on the honest sample. -/
def AEEllipticOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d))
    (a : RegCoeffField d) : Prop :=
  IsAEEllipticFieldOn lam Lam U a.toFun

/-- Public locally a.e.-uniform ellipticity: every triadic cube has
deterministic spatial a.e. ellipticity constants. -/
def AELocallyUniformlyEllipticField {d : ℕ} (a : RegCoeffField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        AEEllipticOn lam Lam (openCubeSet Q) a

/-- A law is supported on locally a.e.-uniformly elliptic fields. -/
def AELocallyUniformlyEllipticLaw {d : ℕ} (P : RestrictionCoeffLaw d) : Prop :=
  ∀ᵐ a ∂P, AELocallyUniformlyEllipticField a

/-- A locally a.e.-uniformly elliptic field is a.e.-elliptic on each half-open
cube as well as on its open core. -/
theorem AELocallyUniformlyEllipticField.exists_aeeEllipticOn_cubeSet
    {d : ℕ} {a : RegCoeffField d}
    (h : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        AEEllipticOn lam Lam (cubeSet Q) a := by
  rcases h Q with ⟨lam, Lam, hlam, hle, hEll⟩
  exact ⟨lam, Lam, hlam, hle, IsAEEllipticFieldOn.cubeSet_of_openCubeSet hEll⟩

/-- A locally a.e.-uniformly elliptic field lies in some countable AEE
quantitative slice on each half-open triadic cube. -/
theorem AELocallyUniformlyEllipticField.exists_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {a : RegCoeffField d}
    (h : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun := by
  rcases h.exists_aeeEllipticOn_cubeSet Q with ⟨lam, _Lam, hlam, _hle, hEll⟩
  exact AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam hEll

/-- A locally a.e.-elliptic law gives an a.s. countable AEE quantitative-slice
cover for each deterministic triadic cube. -/
theorem AELocallyUniformlyEllipticLaw.ae_exists_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : AELocallyUniformlyEllipticLaw P) (Q : TriadicCube d) :
    ∀ᵐ a ∂P, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun := by
  filter_upwards [hP] with a ha
  exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q

/-- **The honest carrier null-measurability bridge.**  Every event of the local
entry-test carrier σ-algebra `LocalSigmaR U` is null-measurable for any carrier
law `P`, because `LocalSigmaR U` is genuinely coarser than the canonical carrier
σ-algebra (`LocalSigmaR_le`) — no hypothesis on `P` is required.

This is a *free* lemma, so it replaces the former `LocalObservableLawCarrier`
hypothesis field of `RestrictionLawCarrier` (which asserted exactly this and was therefore
always derivable — a vestigial hypothesis, removed as an R3-family
strengthening).  Consumers that need a local carrier event to be null-measurable
(the Ch04 `Mu`/coarse-observable measurability handoff) call this directly.

Note (Packet P4b): the P4 report determined that the comap σ-algebra
`localSigma U = comap toFun (fine PointwiseLocalSigma U)` is **not** ≤ the
canonical carrier σ-algebra, so the AEE-slice event has no free
null-measurability bridge along that route.  The honest replacement is genuine
`LocalSigmaR (cubeSet Q)` measurability
of the slice event (`measurableSet_localSigmaR_aeeQuantitativeEllipticSlice`),
which this bridge then promotes to null-measurability. -/
theorem nullMeasurableSet_of_localSigmaR {d : ℕ} (P : RestrictionCoeffLaw d)
    {U : Set (Vec d)} {s : Set (RegCoeffField d)}
    (hs : @MeasurableSet (RegCoeffField d) (LocalSigmaR U) s) :
    NullMeasurableSet s P :=
  (LocalSigmaR_le U s hs).nullMeasurableSet

/-- **The AEE quantitative-slice event is genuinely `LocalSigmaR`-measurable, with
no hypothesis on the law** (Packet P4b).  This is the honest core discovered by
the P4 report: unlike the comap slice field, the entry-test-local `LocalSigmaR`
event is genuinely below the canonical carrier σ-algebra, and its measurability
is established directly by Lebesgue differentiation and the rational-ball average
characterization (`measurableSet_localSigmaR_aeeSlice`).  Being law-independent,
it is a *theorem*, not a `RestrictionLawCarrier` field. -/
theorem measurableSet_localSigmaR_aeeQuantitativeEllipticSlice {d : ℕ}
    (Q : TriadicCube d) (k : ℕ) :
    @MeasurableSet (RegCoeffField d) (LocalSigmaR (cubeSet Q))
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} :=
  Homogenization.measurableSet_localSigmaR_aeeSlice Q k

/-- The single public Chapter 4 law carrier.  The former
`aee_quantitative_slice_measurable` field was law-independent — its content is now
the free theorem `measurableSet_localSigmaR_aeeQuantitativeEllipticSlice` (Packet
P4b, an R3-family strengthening) — and has been removed. -/
structure RestrictionLawCarrier {d : ℕ} (P : RestrictionCoeffLaw d) : Prop where
  isProbability : IsProbabilityMeasure P
  ae_locally_uniformly_elliptic : AELocallyUniformlyEllipticLaw P

/-- A probability law supported on locally a.e.-uniformly elliptic fields is a
Chapter 4 law carrier.  Both former measurability fields (the AEE-slice
measurability and the earlier local-observable measurability) were vestigial —
law-independent and derivable directly — and have been removed. -/
theorem lawCarrier_of_aeLocallyUniformlyElliptic {d : ℕ} {P : RestrictionCoeffLaw d}
    [IsProbabilityMeasure P] (hP : AELocallyUniformlyEllipticLaw P) :
    RestrictionLawCarrier P where
  isProbability := inferInstance
  ae_locally_uniformly_elliptic := hP

namespace RestrictionLawCarrier

/-- Canonical access to the a.s. locally a.e.-uniform ellipticity support of a
Chapter 4 law carrier. -/
theorem ae_locallyUniformlyEllipticField {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier P) :
    ∀ᵐ a ∂P, AELocallyUniformlyEllipticField a :=
  hP.ae_locally_uniformly_elliptic

end RestrictionLawCarrier

/-- Public stationarity assumption `(P1)`. -/
abbrev RestrictionStationaryLaw {d : ℕ} (P : RestrictionCoeffLaw d) : Prop :=
  Homogenization.IsStationaryR P

/-- The explicit restriction-unit-range dependence assumption: independence of
the pointwise restriction σ-algebras of unit-separated measurable sets. -/
abbrev RestrictionUnitRangeDependentLaw {d : ℕ} (P : RestrictionCoeffLaw d) : Prop :=
  Homogenization.IsRestrictionUnitRangeDependentR P

/-- Public isotropy assumption `(P3)`, restricted to signed permutations. -/
abbrev RestrictionIsotropicLaw {d : ℕ} (P : RestrictionCoeffLaw d) : Prop :=
  Homogenization.IsIsotropicInLawR P

/-- Public adjoint-invariance assumption. -/
abbrev RestrictionAdjointInvariantLaw {d : ℕ} (P : RestrictionCoeffLaw d) : Prop :=
  Homogenization.IsAdjointInvariantInLawR P

/-- The combined restriction-lane structural law assumptions, kept separate from
measurability and ellipticity so downstream theorems request only what they use. -/
structure RestrictionStructuralLaw {d : ℕ} (P : RestrictionCoeffLaw d) : Prop where
  stationary : RestrictionStationaryLaw P
  unit_range : RestrictionUnitRangeDependentLaw P
  isotropic : RestrictionIsotropicLaw P
  adjoint_invariant : RestrictionAdjointInvariantLaw P

end Ch04
end Book
end Homogenization
