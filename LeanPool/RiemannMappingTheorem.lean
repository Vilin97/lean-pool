/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/

import LeanPool.RiemannMappingTheorem.Main

/-!
# Riemann Mapping Theorem

Source: url:https://github.com/vbeffara/rMT4
Authors: Vincent Beffara
Status: verified
Main declarations: `RMT`, `main`, `montel`, `hurwitz`
Tags: complex-analysis, conformal-maps, schwarz-lemma
-/

/-!
## Mathematical overview

The Riemann Mapping Theorem states that any non-empty, simply connected open
proper subset of `ℂ` is conformally equivalent to the open unit disk. The
formalisation here proves the analogous statement for connected open proper
subsets `U ⊆ ℂ` that admit primitives (and hence holomorphic logarithms and
square roots): there exists a holomorphic injection `f : ℂ → ℂ` with
`f '' U = ball 0 1`.

The headline theorems are:

* `RMT` — the main theorem, packaging the statement above.
* `main` — the existence of a maximal-derivative injection from a `good_domain`
  to the unit disk, obtained via Montel's theorem and a derivative-maximisation
  argument.
* `montel` — Montel's theorem: a uniformly bounded family of holomorphic
  functions on a domain is normal (totally bounded for compact convergence).
* `hurwitz` — Hurwitz's theorem on locally uniform limits of zero-free
  holomorphic functions, used together with Schwarz's lemma to upgrade the
  maximiser to a surjection onto the open disk.

## Provenance

Imported from <https://github.com/vbeffara/rMT4>. Upstream contains no `sorry`s.
Ported from Lean v4.26.0 to Lean Pool's v4.30.0-rc2.
-/
