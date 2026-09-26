/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Topology.Metrizable.Basic

/-!
# Measurability of exact coarse-source local random variables

All promotions stay on the exact coarse source carrier.  In particular, no
regular-carrier or restriction-sigma bridge is used here.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory

namespace IsSourceLocalRandomVariable

/-- A source-local random variable is measurable for the source global sigma
algebra. -/
theorem measurable {β : Type*} [MeasurableSpace β] {d : ℕ}
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : Source.Coarse.Carrier d → β}
    (hX : IsSourceLocalRandomVariable U hU X) :
    Measurable X :=
  Measurable.mono hX
    (Source.Coarse.localSigma_mono hU MeasurableSet.univ (fun _ _ => Set.mem_univ _)) le_rfl

/-- A source-local random variable is null-measurable under every source law. -/
theorem nullMeasurable {β : Type*} [MeasurableSpace β] {d : ℕ}
    {P : SourceCoeffLaw d} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → β}
    (hX : IsSourceLocalRandomVariable U hU X) :
    NullMeasurable X P := by
  intro s hs
  exact ((hX.measurable) hs).nullMeasurableSet

/-- A source-local random variable is a.e. measurable under every source law. -/
theorem aemeasurable {β : Type*} [MeasurableSpace β]
    {d : ℕ} {P : SourceCoeffLaw d} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → β}
    (hX : IsSourceLocalRandomVariable U hU X) :
    AEMeasurable X P :=
  hX.measurable.aemeasurable

/-- A source-local random variable into a second-countable pseudometrizable
measurable space is a.e. strongly measurable under every source law. -/
theorem aestronglyMeasurable {β : Type*} [TopologicalSpace β]
    [MeasurableSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [OpensMeasurableSpace β] [SecondCountableTopology β]
    {d : ℕ} {P : SourceCoeffLaw d} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → β}
    (hX : IsSourceLocalRandomVariable U hU X) :
    AEStronglyMeasurable X P :=
  hX.measurable.aestronglyMeasurable

end IsSourceLocalRandomVariable

namespace SourceObservable

/-- A bundled source observable is null-measurable under every source law. -/
theorem nullMeasurable {β : Type*} [MeasurableSpace β] {d : ℕ}
    {P : SourceCoeffLaw d} {U : Set (Vec d)} (X : SourceObservable d U β) :
    NullMeasurable X P :=
  X.isLocal.nullMeasurable (P := P)

/-- A bundled source observable is a.e. measurable under every source law. -/
theorem aemeasurable {β : Type*} [MeasurableSpace β]
    {d : ℕ} {P : SourceCoeffLaw d} {U : Set (Vec d)} (X : SourceObservable d U β) :
    AEMeasurable X P :=
  X.isLocal.measurable.aemeasurable

/-- A bundled source observable into a second-countable pseudometrizable
measurable space is a.e. strongly measurable under every source law. -/
theorem aestronglyMeasurable {β : Type*} [TopologicalSpace β]
    [MeasurableSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [OpensMeasurableSpace β] [SecondCountableTopology β]
    {d : ℕ} {P : SourceCoeffLaw d} {U : Set (Vec d)} (X : SourceObservable d U β) :
    AEStronglyMeasurable X P :=
  X.isLocal.measurable.aestronglyMeasurable

end SourceObservable

end Homogenization.Book.Ch04
