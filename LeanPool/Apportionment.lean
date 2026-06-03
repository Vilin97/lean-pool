/-
Copyright (c) 2026 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/

import LeanPool.Apportionment.Basic
import LeanPool.Apportionment.PlausibleInstances

/-!
# Apportionmentlib

Source: url:https://github.com/mdbrnowski/Apportionmentlib
Authors: Michał Dobranowski
Status: verified
Main declarations: `Apportionment.balinski_young`
Tags: social-choice-theory, combinatorics
MSC: 91B12, 91B14
-/

/-!
## Mathematical overview

The library formalizes the basic vocabulary of *apportionment theory*, the part of
social-choice theory that studies how to allocate a fixed number of seats among parties
in proportion to their vote counts. The setup is built around `Election n`, recording a
vector of `n` party vote totals and a positive house size, and `Apportionment n`, the
corresponding seat distributions. An apportionment `Rule` returns a non-empty finite set
of feasible seat allocations satisfying inheritance of zeros and house-size feasibility.

Several rule properties are formalized as type classes — `IsAnonymous`, `IsBalanced`,
`IsConcordant`, `IsDecent`, `IsExact`, `IsQuotaRule`, `IsPopulationMonotone` — and the
two main results are `IsConcordant_of_IsPopulationMonotone` and the *Balinski–Young
impossibility theorem* `Apportionment.balinski_young`: no anonymous quota rule can be
population-monotone. The proof exhibits two explicit four-party elections where any quota
allocation forces the population paradox.

## Provenance

Imported from <https://github.com/mdbrnowski/Apportionmentlib>. Upstream contains no
`sorry`s. Ported from Lean `v4.28.0` to Lean Pool's `v4.30.0-rc2`. The upstream namespace
`Apportionmentlib` was renamed to `Apportionment` and the library root renamed
accordingly.
-/
