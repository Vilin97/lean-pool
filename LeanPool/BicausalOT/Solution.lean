/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
module

public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.MeasurableSelection


/-!
# Solution file: the Kuratowski–Ryll-Nardzewski measurable selection theorem

This module supplies a declaration whose type is exactly the type stated in `Challenge`,
together with its proof.

The proof itself lives in `BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean`,
which imports Mathlib only.  It is the classical Kuratowski–Ryll-Nardzewski argument:

* fix a dense sequence `u : ℕ → Y` (`TopologicalSpace.exists_dense_seq`);
* build measurable, countably-`u`-valued approximate selectors `fₙ = u ∘ gₙ`, with
  `gₙ a` the *least* index `k` for which `Φ a` meets `ball (u k) ((1/2)^n)` and also the
  previous stage's ball — measurability of the least-index operation is
  `MeasurableSelection.measurable_firstIdx`;
* the key measurability step, `MeasurableSelection.step_measurableSet`, splits the test
  set over the countably many measurable fibres `{gₙ = j}`, on each of which the test set
  is cut out by the *fixed* open set `ball (u k) r' ∩ ball (u j) r`, so the weak
  measurability hypothesis applies directly;
* the resulting sequence is uniformly Cauchy (`dist (fₙ a) (fₙ₊₁ a) ≤ (3/2)·(1/2)ⁿ`), its
  pointwise limit is measurable by `measurable_of_tendsto_metrizable`, and it lands in
  `Φ a` because `Φ a` is closed.

The declaration below restates that theorem inside the `MeasurableSelection` namespace so
that its name matches the `Challenge` declaration named in `comparator.json`; the root
`exists_measurable_selection` it delegates to is the audited declaration of the library,
and is one of the theorems covered by the repository's `#print axioms` audit
(`AxiomAudit.lean` and `BicausalOT/AxiomsAudit.lean`), which reports only
`[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open TopologicalSpace

namespace MeasurableSelection

/-- **The Kuratowski–Ryll-Nardzewski measurable selection theorem** (Kechris,
*Classical Descriptive Set Theory*, Theorem 12.13; Srivastava, *A Course on Borel Sets*,
Theorem 5.2.1).

Let `α` be an arbitrary measurable space and `Y` a Polish space, presented as a complete
separable metric space carrying its Borel σ-algebra.  Let `Φ : α → Set Y` have nonempty
closed values and be weakly measurable, i.e. `{a | Φ a ∩ U ≠ ∅}` is measurable for every
open `U ⊆ Y`.  Then `Φ` has a Borel-measurable selection: there exists a measurable
`f : α → Y` with `f a ∈ Φ a` for every `a`. -/
theorem exists_measurable_selection {α : Type*} [MeasurableSpace α] {Y : Type*}
    [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Φ : α → Set Y} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a :=
  _root_.exists_measurable_selection hne hclosed hmeas

end MeasurableSelection
