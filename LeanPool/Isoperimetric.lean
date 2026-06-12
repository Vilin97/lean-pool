/-
Copyright (c) 2026 Jonathan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Ho
-/

import LeanPool.Isoperimetric.Basic
import LeanPool.Isoperimetric.BrunnMinkowski
import LeanPool.Isoperimetric.Isoperimetric
import LeanPool.Isoperimetric.PrekopaLeindler

/-!
# Prekopa-Leindler, Brunn-Minkowski, and the isoperimetric inequality

Source: url:https://terrytao.wordpress.com/2011/09/16/the-brunn-minkowski-inequality-for-nilpotent-groups/
Authors: Jonathan Ho
Status: verified
Main declarations: `prekopa_leindler`, `brunn_minkowski`, `isoperimetric_inequality`
Tags: measure-theory, geometric-inequalities
MSC: 28A75, 52A40, 49Q20
-/

/-!
## Mathematical overview

Following Terence Tao's [blog post on the Brunn–Minkowski inequality for
nilpotent groups]
(https://terrytao.wordpress.com/2011/09/16/the-brunn-minkowski-inequality-for-nilpotent-groups/),
this project formalizes three classical inequalities of measure-theoretic
geometry on Euclidean space `ℝⁿ`:

* `prekopa_leindler` — the Prékopa–Leindler functional inequality for
  `ENNReal`-valued functions, which generalizes Brunn–Minkowski and is proved
  here by reducing to one dimension via the layer-cake formula and then
  inducting on the dimension.
* `brunn_minkowski` — for nonempty measurable sets `A, B ⊆ ℝⁿ`,
  `volume(A)^{1/n} + volume(B)^{1/n} ≤ volume(A + B)^{1/n}`. This is
  obtained by applying Prékopa–Leindler to the indicator functions of
  `A` and `B`.
* `isoperimetric_inequality` — combining Brunn–Minkowski with `A` and an
  `ε`-ball recovers the standard form of the isoperimetric inequality on
  Euclidean space.

## Provenance

Imported from <https://github.com/hojonathanho/isoperimetric>; ported from
Lean v4.26.0-rc2 to Lean Pool's v4.30.0-rc2.
-/
