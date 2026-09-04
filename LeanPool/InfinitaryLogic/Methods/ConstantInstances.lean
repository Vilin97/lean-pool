/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# Constant instances: `instConst`, `closeBy`, and their substitution algebra

The two closing operations by the auxiliary constants of `L[[ℕ]]`, in a neutral module below
both the interpolation layer and the countable-completion kernel:

* `instConst c ψ` — open the single bound variable of `ψ : BoundedFormulaω Empty 1` and substitute
  the constant `c_c`;
* `closeBy φ τ` — open all `n` bound variables of `φ : BoundedFormulaω Empty n` and substitute the
  constants `c_{τ i}`.

Their semantic consumer lemmas (`realize_instConst`, `realize_closeBy`, …) stay in the modules
that own the structures they realize in.  This module holds only syntax: the
**connective/universal** algebra of `closeBy` — how it commutes with the connectives, what the
arity-one remainder of a closed universal is, and that the constant instance of that remainder is
`closeBy` at the extended tuple.  Atomic template lemmas (closing an equality or relation template
gives `constEq` / `relInst`) belong with those atoms, above this module.

The public surface is deliberately small: `instConst`, `closeBy`, the `closeBy_*` commutations,
`closeBy_zero`, `instConst_eq_closeBy`, `instConst_closeBy_all_remainder`, and the generic
substitution laws `Term.subst_subst` / `Term.subst_relabel` / `Term.relabel_subst` /
`BoundedFormulaω.subst_subst`.  Everything else is proof scaffolding and is private.

## The `all` case

`closeBy φ.all τ` is `(remainder).all`, where the remainder is `φ` opened, relabeled so that the
last bound variable stays bound, and closed by `τ`.  The instance of that remainder at a constant
`c` must be `closeBy φ (Fin.snoc τ c)` — this is what makes universal-instance closure of a
constants-expanded universe follow from a fragment's `all_mem`.  Proving it directly fights
`castLE` inside `BoundedFormulaω.relabel`, so instead:

* a private `closeWith ρ φ` closes bound variables by a term assignment `ρ`, by structural
  recursion with **no** `relabel` of formulas; it depends on `ρ` only pointwise and composes;
* one private bridge lemma identifies `((openBounds φ).relabel g).subst τ'` with a `closeWith` for
  the standard splitting `g`, using the two relabel-composition lemmas of `Operations.lean`;
* `closeBy`, its remainder, and `instConst` are then all `closeWith`s, and
  `instConst_closeBy_all_remainder` is the composition law plus a pointwise check.
-/

universe u v u'

namespace FirstOrder.Language

open FirstOrder Structure

/-! ## Term-level substitution algebra -/

namespace Term

variable {L : Language.{u, v}} {α β γ : Type u'}

end Term

/-! ## Formula-level substitution composition -/

namespace BoundedFormulaω

variable {L : Language.{u, v}} {α β γ : Type u'} {n : ℕ}

end BoundedFormulaω

variable {L : Language.{0, 0}}

/-! ## The closing operations -/

/-- The constant instance `ψ(c)`: open the bound variable of `ψ` and substitute the constant
`c_c`. -/
def instConst (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1) : L[[ℕ]].Sentenceω :=
  (ψ.openBounds).subst (fun _ => constTerm c)

/-- The closing substitution of a bounded formula by constants. -/
noncomputable def closeBy {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    L[[ℕ]].Sentenceω :=
  (φ.openBounds).subst (fun i => constTerm (τ i))

/-! ## Definitional commutations of `closeBy`

Each holds by unfolding `openBounds` and `subst` on the constructor.  The `all` case exhibits the
arity-one remainder explicitly; relating its `instConst` to `closeBy` at the extended parameter
tuple is a separate lemma about `openBounds`, proved where it is consumed. -/

section CloseBy

variable {n : ℕ}

end CloseBy

/-! ## `closeWith`: closing bound variables by a term assignment, without relabeling formulas -/

/-! ## Composition -/

/-! ## The bridge to `openBounds`

`closeBy`, `instConst`, and the arity-one remainder of `closeBy_all` are all
`((openBounds φ).relabel g).subst τ'` for a splitting `g`.  This is the one place where
`relabel` of a formula — and hence `castLE` — is met; it is discharged by the two composition
lemmas of `Operations.lean`, exactly as in `openBounds_relabel_sumInr`. -/

/-! ## `closeBy`, its arity-one remainder, and `instConst`, as `closeWith` -/

end FirstOrder.Language
