/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ResolventBound
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The spectrum is closed

Openness of the resolvent set is proved by the canonical core in
`ForTauCeti.Analysis.Normed.Operator.Resolvent.Unbounded`
(`TauCeti.LinearPMap.isOpen_resolventSet`), by the usual Neumann-series
perturbation.  This file draws the consequences for the **spectrum**, which is
this package's notion rather than the core's: it is closed, and its real slice is
closed and hence measurable.

## Why it is needed

Measurability.  Every consumer that wants to feed a spectral set to a
projection-valued measure — `specProjection hA (Complex.ofReal ⁻¹' spectrum A)`,
and in particular the Rosenblum argument, which needs a *measurable* set
separating two disjoint spectra — needs the spectrum to be a Borel set first,
and closedness is how that is obtained.

## Provenance

* **Original repository:** none — **authored in place** in the AIQ DKPS
  formalization (`https://github.com/AIQ-Kitware/aiq-dkps-formalization`),
  commit `9be75beb`, for staging into Tau Ceti.
* **Original module:** none; written directly at this path.
* **Original authors / copyright / licence:** Copyright (c) 2026 Kitware, Inc.;
  `Authors: Jon Crall, Claude Opus 5`; Apache 2.0 (this repository's `LICENSE`).
  No third-party code is incorporated, so no donor notice is carried.
* **Extraction class:** *authored in place*, for upstreaming to Tau Ceti.
* **Relation to existing libraries:** Mathlib proves the bounded analogue,
  `spectrum.isOpen_resolventSet`. The `LinearPMap` statement, which Mathlib does
  not have, is now proved by the canonical resolvent core; this module carries
  only the spectrum-side consequences, the spectrum being a notion the core does
  not define. An earlier version of this file proved openness itself, by the same
  Neumann-series perturbation, together with the Neumann-factor helpers it
  needed; those are superseded and have been removed. Spectra did not influence
  the selection or the proof.
* **Semantic differences from a donor:** not applicable.
-/

@[expose] public section

open scoped Topology

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **The spectrum is closed.** -/
theorem isClosed_spectrum (A : E →ₗ.[𝕜] E) : IsClosed (spectrum A) := by
  rw [spectrum_eq_compl, isClosed_compl_iff]
  exact isOpen_resolventSet A

section RealPoints

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The real points of the spectrum form a closed, hence measurable, subset of
`ℝ` — the form every spectral-measure consumer needs. -/
theorem isClosed_realSpectrum (A : F →ₗ.[ℂ] F) :
    IsClosed (Complex.ofReal ⁻¹' spectrum A) :=
  (isClosed_spectrum A).preimage Complex.continuous_ofReal

/-- The real spectrum is measurable, being closed.  This is the enabling fact for defining spectral
measures on it; Mathlib has the open-resolvent-set statement only for bounded operators. -/
theorem measurableSet_realSpectrum (A : F →ₗ.[ℂ] F) :
    MeasurableSet (Complex.ofReal ⁻¹' spectrum A) :=
  (isClosed_realSpectrum A).measurableSet

end RealPoints

end LinearPMap
end TauCeti
