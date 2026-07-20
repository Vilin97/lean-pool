/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Global

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian`

Thin re-export of the Riemannian Rellich–Kondrachov proof, split into focused submodules:

* `RellichKondrachovRiemannian.Transport`: `L²` transport (change of measure, `extendByZero` glue).
* `RellichKondrachovRiemannian.Chartwise`: chartwise compactness via Euclidean Rellich on `volume`.
* `RellichKondrachovRiemannian.Global`: finite-atlas assembly and the final compactness theorem.
-/

