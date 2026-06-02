/-
Copyright (c) 2026 Abdullah Uyu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdullah Uyu
-/

import LeanPool.Desargues.Basic

/-!
# Morphisms of projective geometries

Defines isomorphisms of projective geometries as bijections preserving the
collinearity relation.
-/

open Basic

/-- An isomorphism of projective geometries is a bijective map `f : G₁ → G₂`
satisfying `ell₁ a b c ↔ ell₂ (f a) (f b) (f c)`. When `G₁ = G₂` one says that
`f` is a collineation. (p. 27) -/
class PG_Iso
  {G₁ : Type*}
  {G₂ : Type*}
  {ell₁ : G₁ → G₁ → G₁ → Prop}
  {ell₂ : G₂ → G₂ → G₂ → Prop}
  [ProjectiveGeometry G₁ ell₁]
  [ProjectiveGeometry G₂ ell₂]
  (f : G₁ → G₂) where
  bij : Function.Bijective f
  pres_col : ∀ (a b c : G₁), ell₁ a b c ↔ ell₂ (f a) (f b) (f c)
