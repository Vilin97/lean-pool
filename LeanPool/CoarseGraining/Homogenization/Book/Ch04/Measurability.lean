/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionObservable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Metrizable.Basic

/-! # Measurability -/

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Law-relative measurability promotion (carrier re-type, Packet P3)

This is the canonical Ch4 bridge:

`IsRestrictionLocalRandomVariable U hU X → AEMeasurable X P → AEStronglyMeasurable X P`.

On the honest-fields carrier the promotion is genuine: the restriction σ-algebra
`RestrictionSigmaR U hU` is contained in the canonical carrier σ-algebra
(`restrictionSigmaR_le`), so a restriction-local random variable is honestly
measurable, hence null- and a.e.-strongly measurable.  This is unconditional in
the law: the former `LocalObservableLawCarrier` hypothesis was always derivable
(a vestigial hypothesis, Packet P4 R3-family strengthening) and has been dropped
from these bridges — they now hold for *every* carrier law.

Later chapters should not introduce section-local copies of this bridge.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace IsRestrictionLocalRandomVariable

/-- A restriction-local random variable is null-measurable under any carrier
law. -/
theorem nullMeasurable {β : Type*} [MeasurableSpace β] {d : ℕ}
    {P : RestrictionCoeffLaw d}
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : RegCoeffField d → β}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    NullMeasurable X P := by
  intro s hs
  have hXm : Measurable X :=
    Measurable.mono hX (restrictionSigmaR_le U hU) le_rfl
  exact (hXm hs).nullMeasurableSet

/-- A local random variable with countably generated target sigma algebra is
a.e. measurable under any carrier law. -/
theorem aemeasurable {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated β] {d : ℕ}
    {P : RestrictionCoeffLaw d}
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : RegCoeffField d → β}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    AEMeasurable X P :=
  (hX.nullMeasurable (P := P)).aemeasurable

/-- A local random variable into a second-countable pseudometrizable measurable
space is a.e. strongly measurable under any carrier law. -/
theorem aestronglyMeasurable {β : Type*} [TopologicalSpace β]
    [MeasurableSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [OpensMeasurableSpace β] [SecondCountableTopology β]
    [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : RestrictionCoeffLaw d}
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : RegCoeffField d → β}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    AEStronglyMeasurable X P :=
  (hX.aemeasurable (P := P)).aestronglyMeasurable

end IsRestrictionLocalRandomVariable

namespace RestrictionLawCarrier

/-- Dot-notation promotion from local-test measurability to null measurability. -/
theorem nullMeasurable_of_isLocalRandomVariable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {P : RestrictionCoeffLaw d}
    (_hP : RestrictionLawCarrier P) {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → β} (hX : IsRestrictionLocalRandomVariable U hU X) :
    NullMeasurable X P :=
  hX.nullMeasurable (P := P)

/-- Dot-notation promotion from local-test measurability to a.e.
measurability. -/
theorem aemeasurable_of_isLocalRandomVariable
    {β : Type*} [MeasurableSpace β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : RestrictionCoeffLaw d} (_hP : RestrictionLawCarrier P)
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : RegCoeffField d → β}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    AEMeasurable X P :=
  hX.aemeasurable (P := P)

/-- Dot-notation promotion from local-test measurability to a.e. strong
measurability. -/
theorem aestronglyMeasurable_of_isLocalRandomVariable
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : RestrictionCoeffLaw d} (_hP : RestrictionLawCarrier P)
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : RegCoeffField d → β}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    AEStronglyMeasurable X P :=
  hX.aestronglyMeasurable (P := P)

/-- Bundled-observable promotion to null measurability. -/
theorem nullMeasurable_observable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier P) {U : Set (Vec d)} (X : RestrictionObservable d U β) :
    NullMeasurable X P :=
  hP.nullMeasurable_of_isLocalRandomVariable X.isLocal

/-- Bundled-observable promotion to a.e. measurability. -/
theorem aemeasurable_observable
    {β : Type*} [MeasurableSpace β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {U : Set (Vec d)} (X : RestrictionObservable d U β) :
    AEMeasurable X P :=
  hP.aemeasurable_of_isLocalRandomVariable X.isLocal

/-- Bundled-observable promotion to a.e. strong measurability. -/
theorem aestronglyMeasurable_observable
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {U : Set (Vec d)} (X : RestrictionObservable d U β) :
    AEStronglyMeasurable X P :=
  hP.aestronglyMeasurable_of_isLocalRandomVariable X.isLocal

/-- Canonical access to AEE quantitative slice local measurability, now the
law-independent honest form (Packet P4b): genuine `LocalSigmaR (cubeSet Q)`
measurability.  The `RestrictionLawCarrier` argument is retained only for the dot-notation
call site; the content no longer depends on the law. -/
theorem measurableSet_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (_hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (k : ℕ) :
    @MeasurableSet (RegCoeffField d) (LocalSigmaR (cubeSet Q))
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} :=
  measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k

/-- A Chapter 4 law carrier gives the a.s. countable AEE quantitative-slice
cover on each deterministic triadic cube. -/
theorem ae_exists_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) (Q : TriadicCube d) :
    ∀ᵐ a ∂P, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun :=
  hP.ae_locally_uniformly_elliptic.ae_exists_aeeQuantitativeEllipticSlice_cubeSet Q

end RestrictionLawCarrier

end Ch04
end Book
end Homogenization
