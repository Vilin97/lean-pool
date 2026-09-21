/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Raw
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# PoincareCurvature.Basic

This module packages the first concrete curvature-theoretic layer of the
roadmap:

- the section-valued operation `∇_X σ`
- the raw curvature commutator `∇_X∇_Yσ - ∇_Y∇_Xσ - ∇_[X,Y]σ`
- the bundled curvature tensor `curvatureTensor`
- Ricci and scalar curvature contractions on the tangent bundle
- metric compatibility interfaces for Riemannian vector bundles
- torsion-free and Levi-Civita predicates for affine connections
- uniqueness of Levi-Civita connections, expressed as vanishing of the difference one-form

The root module `PoincareCurvature` additionally exports the next static layer
(Levi-Civita existence, sectional curvature, and the first and second Bianchi
identities), the time-dependent geometry layer for one-parameter families of
sections, covariant derivatives, smooth Riemannian metrics, Levi-Civita
families, tangent-bundle curvature data, a `C^0` local-frame criterion for
continuous bundle sections together with compact-piece `ContinuousMap`
packaging of local coefficients, cover-level compatible compact coordinate
families, their closed complete compatibility kernel on finite compact covers,
the resulting finite-cover equivalence between continuous sections and
compatible compact coordinate families (equivalently, with the closed kernel
model), together with transport of the induced additive, module, normed, and
complete structure to a dedicated continuous-section wrapper, and a
section-smoothing layer with
local-to-global convex gluing, trivial-bundle and open-set smoothing, local
smoothing inside bundle trivializations, and global smoothing into open
fiberwise convex subsets of the total space, together with intrinsic
fiberwise-`ε` approximation for continuous sections of smooth Riemannian vector
bundles.
-/
