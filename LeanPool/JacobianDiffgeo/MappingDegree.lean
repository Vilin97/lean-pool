/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.MappingDegree.Basics
import LeanPool.JacobianDiffgeo.MappingDegree.RootCounting
import LeanPool.JacobianDiffgeo.MappingDegree.Ramification
import LeanPool.JacobianDiffgeo.MappingDegree.LocalStructure
import LeanPool.JacobianDiffgeo.MappingDegree.LocalConstancy
import LeanPool.JacobianDiffgeo.MappingDegree.Degree
import LeanPool.JacobianDiffgeo.MappingDegree.Covering

/-!
# mapping-degree: the mapping degree of a holomorphic map between compact Riemann surfaces
(namespace `RS`)

API summary (see `docs/design/mapping-degree.md`). Standing hypotheses throughout: `F : X → Y`
between compact connected Riemann surfaces (`X`) and Riemann surfaces (`Y`), with
`hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F` and global nonconstancy `hne : ¬ ∃ c, ∀ x, F x = c` (the bridge
to every local-multiplicity hypothesis is `not_eventuallyConst`).

* **Basics**: `fiberMultSum F y` (`finsum` of `multiplicity` over the fiber; junk `0` for
  constant `F`); fibers of nonconstant `F` are closed/discrete/finite (`fiber_finite`);
  re-exports `isOpenMap_of_not_const'`, `surjective_of_not_const'`; surface perfectness instance
  `nhdsNE_neBot_of_chartedSpace`.
* **RootCounting** (mathlib-only): the planar identity `sum_toNat_analyticOrderAt_pow_sub` — the
  total multiplicity of `z ↦ z ^ k` over any `w : ℂ` is `k`.
* **Ramification**: `ramificationLocus`, `branchLocus`, `IsRegularValue`; all finite/cofinite as
  expected (`ramificationLocus_finite`, `branchLocus_finite`, `setOf_isRegularValue_mem_cofinite`,
  `dense_setOf_isRegularValue`).
* **LocalStructure**: `FiberStack F y₀` — the stack of adapted charts over an arbitrary fiber
  (existence: `exists_fiberStack`), Forster's 4.24-proof mechanism generalized to count WITH
  multiplicity at every point of `Y`, branched or not.
* **LocalConstancy**: the heart — `isLocallyConstant_fiberMultSum`, and THE well-definedness
  theorem `fiberMultSum_const` (`fiberMultSum` is independent of the basepoint).
* **Degree**: `degree F : ℕ` (well-defined by `fiberMultSum_eq_degree`; `0` for constant maps);
  `ncard_fiber_of_isRegularValue` (fiber cardinality = degree over regular values);
  degree-1 ⇒ bijective ⇒ homeomorphism (`bijective_of_degree_eq_one`,
  `homeomorphOfDegreeEqOne`, `isHomeomorph_of_degree_eq_one`); `degree_comp` (multiplicativity,
  statement bank, needs the extra instance `[CompactSpace Y]`).
* **Covering**: `isCoveringMapOn_compl_branchLocus` — `F` is a covering map off the (finite)
  branch locus (mathlib's `IsCoveringMapOn.of_openPartialHomeomorph`); downstream may compose
  with mathlib's `IsCoveringMapOn.isCoveringMap_restrictPreimage` and
  `Topology/Homotopy/Lifting.lean` for path/homotopy lifting.

Downstream notes: `ContMDiff.degree` (final challenge API) is the one-line wrapper `RS.degree f`
— junk-`0` on constants holds definitionally, so the wrapper needs no case split.
proper-map-degree reads `fiberMultSum_eq_degree` at `y := 0`/`y := ∞` on `ℙ¹` for the
zeros-minus-poles identity; meromorphic-trace/form-trace-tower consume the whole `FiberStack`
structure; paths-and-integrals/abel-weak consume `branchLocus_finite` and
`isCoveringMapOn_compl_branchLocus`.
-/
