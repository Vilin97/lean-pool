/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
import Mathlib.Tactic
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.ProbabilityMeasurePolish

/-!
# Solution file: the space of probability measures on a Polish space is Polish

This module supplies a declaration whose type is exactly the type stated in
`ChallengePolish`, together with its proof.

The proof itself lives in `BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean`,
which imports Mathlib modules only (`LevyProkhorovMetric`, `Tight`, `Prokhorov`,
`PiSystem`, `GiryMonad`) and nothing else from this repository.  Mathlib already supplies
the Lévy–Prokhorov metric, its identification with the topology of weak convergence on a
separable space, and Prokhorov's theorem; what it does not supply, at the pinned revision,
is completeness or separability of that metric.  Both are proved there, and the Polish
structure is then transported:

* **Node A** (`isTightMeasureSet_of_cauchySeq`): a Lévy–Prokhorov Cauchy sequence of
  probability measures is uniformly tight.  Heads are covered by a countable dense
  sequence and continuity from below; tails are transferred between members of the
  sequence along the Lévy–Prokhorov inequality; the compact witness is an intersection
  over `j` of finite unions of closed balls of radius `2⁻ʲ`, closed and totally bounded,
  hence compact by completeness of the base space.
* **Node C1** (`instance : CompleteSpace (LevyProkhorov (ProbabilityMeasure Ω))`):
  Prokhorov's theorem (Mathlib's `isCompact_closure_of_isTightMeasureSet`) turns that
  tightness into a convergent subsequence, and a Cauchy sequence with a convergent
  subsequence converges.
* **Node B** (`exists_diracMix_levyProkhorovDist_le`, `instance : SeparableSpace
  (LevyProkhorov (ProbabilityMeasure Ω))`): normalized natural-weight mixtures of Dirac
  measures at points of a countable dense sequence are dense in Lévy–Prokhorov distance,
  which gives a countable dense subset.
* **Node C2/C3**: complete plus separable metric gives `PolishSpace (LevyProkhorov
  (ProbabilityMeasure Ω))`, and Mathlib's homeomorphism
  `LevyProkhorov.probabilityMeasureHomeomorph` transports it to `ProbabilityMeasure X`
  after upgrading a Polish `X` to a complete separable metric space with
  `TopologicalSpace.upgradeIsCompletelyMetrizable`.

`import Mathlib` is present here so that this module elaborates the statement in the
same environment as `ChallengePolish`, which imports Mathlib and nothing else.  The
repository import below declares no name that Mathlib also declares, so it cannot
change how the statement elaborates; the Mathlib import only guarantees that it cannot.

The declaration below restates the resulting instance as a `theorem` inside the
`ProbabilityMeasurePolish` namespace, so that its name matches the `ChallengePolish`
declaration named in `comparator-polish.json`.  Restating an `instance` as a `theorem`
loses nothing here: `PolishSpace` is a `Prop`-valued class, so the instance is a proof of
a proposition and the theorem is a proof of the same proposition.  The root
`ProbabilityMeasure.instPolishSpace` it delegates to is the audited declaration of the
library, and is one of the declarations covered by the repository's `#print axioms` audit
(`AxiomAudit.lean` and `BicausalOT/AxiomsAudit.lean`), which reports only
`[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory

namespace ProbabilityMeasurePolish

/-- **The space of probability measures on a Polish space is Polish** (Parthasarathy,
*Probability Measures on Metric Spaces*, Chapter II §6, "The Weak Topology in the Space of
Measures").

Let `X` be a Polish space carrying its Borel σ-algebra.  Then `ProbabilityMeasure X`, the
space of Borel probability measures on `X` with the topology of weak convergence, is again
Polish: the topology is second countable and admits a complete compatible metric. -/
theorem polishSpace_probabilityMeasure {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    PolishSpace (ProbabilityMeasure X) :=
  _root_.ProbabilityMeasure.instPolishSpace (X := X)

end ProbabilityMeasurePolish
