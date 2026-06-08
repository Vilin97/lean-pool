/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# Petersson inner product (project-local SL(2, ℤ) shims)

The Petersson lemmas from the ForMathlib draft have been upstreamed into
`Mathlib.NumberTheory.ModularForms.Petersson`.  Mathlib phrases them for a
`Γ : Subgroup (GL (Fin 2) ℝ)`
with `[Γ.HasDetOne]`, whereas the rest of this project still works with a
`Γ : Subgroup SL(2, ℤ)`.  We provide thin wrappers that translate the SL version into the GL one.
-/

open ModularForm Complex UpperHalfPlane MatrixGroups

open scoped Real ComplexConjugate

namespace ModularFormClass

lemma petersson_continuous (k : ℤ) (Γ : Subgroup SL(2, ℤ)) {F F' : Type*}
    [FunLike F ℍ ℂ] [ModularFormClass F Γ k]
    [FunLike F' ℍ ℂ] [ModularFormClass F' Γ k] (f : F) (f' : F') :
    Continuous (petersson k f f') :=
  UpperHalfPlane.petersson_continuous k
    (ModularFormClass.holo f).continuous (ModularFormClass.holo f').continuous

end ModularFormClass
