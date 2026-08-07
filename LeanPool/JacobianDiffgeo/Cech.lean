/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Covers
import LeanPool.JacobianDiffgeo.Cech.Cochains
import LeanPool.JacobianDiffgeo.Cech.H0
import LeanPool.JacobianDiffgeo.Cech.Refinement
import LeanPool.JacobianDiffgeo.Cech.Colimit
import LeanPool.JacobianDiffgeo.Cech.Injectivity
import LeanPool.JacobianDiffgeo.Cech.Window
import LeanPool.JacobianDiffgeo.Cech.WindowRank
import LeanPool.JacobianDiffgeo.Cech.Skyscraper
import LeanPool.JacobianDiffgeo.Cech.SixTerm

/-!
# cech-cohomology (CC8): `H¹(D)` as a directed colimit over finite covers (namespace `RS.Cech`)

API summary (see `docs/design/cech-cohomology.md`):

* **Covers** (`Covers.lean`): `FinCover Ω` (`Fin n`-indexed opens covering `Ω`), the refinement
  `Preorder`/`IsDirectedOrder`, `IsChartDisk`/`FinCover.IsGood` (cofinal good covers,
  `exists_good_refinement(_closure)`), `FinCover.IsAdapted` (`exists_adapted_refinement`).
* **Cochains** (`Cochains.lean`): `LinSysOn.restrictL`, `C0`/`C1`/`C2` (full-product convention),
  `d0`/`d1`, `Z1`/`B1`/`H1Cover` (cover-level Čech `H¹(𝒰,D)`), `MeroGermOn.congrSet` [Compat].
* **`H⁰`** (`H0.lean`): `h0EquivLinSysOn`/`h0Equiv` — `H⁰(𝒰,D) ≃ L(D)` via sheaf gluing.
* **Refinement** (`Refinement.lean`): `resC0`/`resC1`/`resZ1`/`resH1`, the cocycle-relation
  workhorse `Z1.rel_res`, **Forster 12.3** (`resH1_indep`) and the functor laws
  (`resH1_id`/`resH1_comp`) that make `H1Cover` a `DirectedSystem`.
* **Colimit** (`Colimit.lean`): **`H1 D`**, the directed colimit (CC8, frozen), `toH1`,
  `exists_rep(_good/_refined)`, `H1.induction_on`, `H1.lift` (universal property),
  `H1Incl` (`D`-monotone functoriality) with `H1Incl_id`/`H1Incl_comp`.
* **Injectivity** (`Injectivity.lean`): **Forster 12.4** — `resH1_injective` (sheaf-axiom
  gluing argument via `injPatch`/`exists_injGlue`), `toH1_injective`/`toH1_eq_zero_iff`,
  `subsingleton_H1_iff`.
* **Window** (`Window.lean`): `ordGe`/`tailGerm`/`leadCoeff`, `WindowAt`/`Window` (the abstract
  skyscraper data), `windowMap` and its exactness/injectivity against `L(D)`/`L(D')`.
* **WindowRank** (`WindowRank.lean`): the `θ`-basis dimension counts `finrank_windowAt`
  (via an explicit one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ`, no
  independence/spanning argument) and `finrank_window`, plus the `FiniteDimensional` instances.
* **Skyscraper** (`Skyscraper.lean`): the Mittag-Leffler atom `mlClass` (`C1.MemLD`/`C1.retype`),
  its linearity and `D`-functoriality, and the vanishing criterion `mlClass_eq_zero_iff`
  (both directions — the `⇒` half uses `toH1_injective`).
* **SixTerm** (`SixTerm.lean`): the full six-term skyscraper fragment
  `0 → L(D) → L(D') → Window D D' → H¹(D) → H¹(D') → 0` (design §6.9(c)-(g)) —
  `exists_tail_approx` ("Lemma B", finite Laurent tails by iterated leading-coefficient
  subtraction), the `Realizes` predicate + `windowDefect` (D7), `exists_realization`
  (adapted-cover realization), `mlClass_eq_of_realizes` ("Lemma A", realization-independence),
  the connecting map **`windowConnect : Window D D' →ₗ[ℂ] H1 D`** with its working form
  `windowConnect_spec`, the exactness statements `exact_windowMap_windowConnect` /
  `exact_windowConnect_H1Incl`, and `H1Incl_surjective` (part (g) — no `H²`, no long exact
  sequence, no snake lemma), via `memLD_of_isAdapted` + the general retype lemmas
  `C1.retype_mem_Z1'`/`h1CoverIncl_mk_retype`.

The unit is **complete**: every export above (including Forster 12.4 injectivity, the window
dimension counts, and the full six-term fragment, all previously deferred) is proved with zero
sorries.
-/
