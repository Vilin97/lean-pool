/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# Constant instances

This neutral module defines the two closing operations by the auxiliary constants of `L[[ℕ]]`:

* `instConst c ψ` — open the single bound variable of `ψ : BoundedFormulaω Empty 1` and substitute
  the constant `c_c`;
* `closeBy φ τ` — open all `n` bound variables of `φ : BoundedFormulaω Empty n` and substitute the
  constants `c_{τ i}`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- The constant instance `ψ(c)`: open the bound variable of `ψ` and substitute the constant
`c_c`. -/
def instConst (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1) : L[[ℕ]].Sentenceω :=
  (ψ.openBounds).subst (fun _ => constTerm c)

/-- The closing substitution of a bounded formula by constants. -/
noncomputable def closeBy {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    L[[ℕ]].Sentenceω :=
  (φ.openBounds).subst (fun i => constTerm (τ i))

end FirstOrder.Language
