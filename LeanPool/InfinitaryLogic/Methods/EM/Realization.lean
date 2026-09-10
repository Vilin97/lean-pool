/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.EM.Template
import LeanPool.InfinitaryLogic.Methods.Henkin.Construction
import Mathlib.Data.Finset.Sort

/-!
# Template-to-`L[[J]]`-theory bridge for Lω₁ω

For each Lω₁ω template `T : Lomega1omegaTemplate L` and each linearly ordered
index type `J`, this file builds the set of `L[[J]]`-sentences whose models are
exactly the `L[[J]]`-structures whose constants realize `T`. The bridge
consists of:

- `templateSentence φ t`: the `L[[J]]`-sentence "`φ` holds on the constants
  indexed by the increasing tuple `t : Fin n ↪o J`".
- `realize_templateSentence`: the semantic bridge — realizing
  `templateSentence φ t` in an `L[[J]]`-expansion of an `L`-structure `M`
  (built from a function `σ : J → M`) is equivalent to realizing the
  underlying Lω₁ω formula `φ` on the tuple `σ ∘ t`.
- `templateTheory T J`: the set of `L[[J]]`-sentences obtained by including,
  for each `(n, φ, t)`, either `templateSentence φ t` (if `T.truth φ`) or its
  negation (if `¬ T.truth φ`).
- `IsLomega1omegaIndiscernible.templateTheory_finitelySatisfiable`: when the
  template comes from an indiscernible sequence indexed by an infinite linear
  order, every finite subset of the resulting template theory is satisfiable
  in the source model.

This file does **not** turn the template into a single model — that step is
blocked both by uncountable `J` (the language `L[[J]]` has uncountably many
constant symbols) and, even for countable `J`, by the fact that `templateTheory T J`
inherits the continuum size of the Lω₁ω formula syntax. Any future
model-realizing tranche will need to restrict to a countable sub-theory.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-! ### Section 1: a `Fin n` order-embedding into any infinite linear order -/

/-! ### Section 2: `templateSentence` — the L[[J]]-sentence "φ on the constants of `t`" -/

namespace Lomega1omegaTemplate

variable {J : Type u} [LinearOrder J]

/-- The `L[[J]]`-sentence expressing "`φ` holds when its `n` bound variables are
interpreted as the constants `c_{t 0}, …, c_{t (n-1)}`". Built by lifting `φ`
to `L[[J]]`, opening its bound variables, and substituting them with the
closed terms for the constants `t 0, …, t (n-1)`. -/
def templateSentence
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    L[[J]].Sentenceω :=
  let φ' : L[[J]].BoundedFormulaω Empty n := φ.mapLanguage (L.lhomWithConstants J)
  let φ'' : L[[J]].Formulaω (Fin n) := φ'.openBounds
  let tf : Fin n → L[[J]].Term Empty :=
    fun i => Term.func (Sum.inr (t i) : L[[J]].Functions 0) Fin.elim0
  φ''.subst tf

end Lomega1omegaTemplate

/-! ### Section 3: `realize_templateSentence` — semantic bridge to `φ.Realize` -/

/-- Realizing `templateSentence φ t` in an `L[[J]]`-expansion of `M` (built from
a function `σ : J → M` via `constantsOn.structure σ`) is equivalent to realizing
`φ` itself on the tuple `σ ∘ t : Fin n → M`. The proof composes
`realize_subst`, `realize_openBounds`, and `realize_mapLanguage`. -/
theorem realize_templateSentence
    {M : Type*} [L.Structure M]
    {J : Type u} [LinearOrder J] (σ : J → M)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    letI : (constantsOn J).Structure M := constantsOn.structure σ
    Sentenceω.Realize (Lomega1omegaTemplate.templateSentence φ t) M ↔
      φ.Realize (Empty.elim : Empty → M) (σ ∘ t) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  -- Unfold templateSentence and Sentenceω.Realize
  change BoundedFormulaω.Realize _ Empty.elim Fin.elim0 ↔ _
  rw [Lomega1omegaTemplate.templateSentence, BoundedFormulaω.realize_subst]
  -- The substituted function is definitionally `σ ∘ t` because each constant
  -- term `Sum.inr (t i)` evaluates to `σ (t i)` via `constantsOn.structure σ`.
  -- Now we need to dispose of the `openBounds` and `mapLanguage` layers.
  -- After realize_subst, the goal is:
  --   BoundedFormulaω.Realize ((φ.mapLanguage _).openBounds) (σ ∘ t) Fin.elim0 ↔
  --     φ.Realize Empty.elim (σ ∘ t)
  -- which equals (definitionally) Formulaω.Realize ((φ.mapLanguage _).openBounds) (σ ∘ t).
  exact (realize_openBounds _ _).trans
        (BoundedFormulaω.realize_mapLanguage _ _ _ _)

/-! ### Section 4: `templateTheory` — the L[[J]]-theory pinning down the template -/

namespace Lomega1omegaTemplate

variable {J : Type u} [LinearOrder J]

/-- The restricted template theory: like `templateTheory`, but only includes
sentences for formulas whose `(arity, φ)`-pair lies in the family `Γ`. When
`Γ` and `J` are both countable, the resulting theory is countable (see
`templateTheoryOn_countable`), making it a candidate input to
`model_existence` — which the full `templateTheory` can never be. -/
def templateTheoryOn
    (T : Lomega1omegaTemplate L)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n))
    (J : Type u) [LinearOrder J] :
    Set L[[J]].Sentenceω :=
  { σ : L[[J]].Sentenceω |
      ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J),
        ⟨n, φ⟩ ∈ Γ ∧
        ((T.truth φ ∧ σ = templateSentence φ t) ∨
         (¬ T.truth φ ∧ σ = (templateSentence φ t).not)) }

end Lomega1omegaTemplate

/-! ### Section 5: finite satisfiability of `templateTheory` in the source model -/

-- Admissible/Barwise adapter theorems (_of_fragment, _of_fullFragment,
-- _of_compact) have been moved to Methods/EM/FragmentAdapter.lean to keep
-- the Countable bundle free of admissible-fragment imports.

/-! ### Section 7: sequence-indexed wrappers

Convenience wrappers over `templateTheoryOn` specialized to a family given as a
sequence `s : ℕ → Σ n, L.BoundedFormulaω Empty n`. The payoff is ergonomic: the
countability of `Set.range s` is automatic, so `templateTheoryOfSeq_countable`
drops the `Γ.Countable` hypothesis that `templateTheoryOn_countable` requires. -/

namespace Lomega1omegaTemplate

variable {J : Type u} [LinearOrder J]

/-- Sequence-based restricted template theory: same content as
`templateTheoryOn T (Set.range s) J`, with a dedicated name for callers that
want to hand a sequence rather than a set. -/
def templateTheoryOfSeq
    (T : Lomega1omegaTemplate L)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (J : Type u) [LinearOrder J] :
    Set L[[J]].Sentenceω :=
  T.templateTheoryOn (Set.range s) J

end Lomega1omegaTemplate

-- Admissible/Barwise adapter theorems for the seq API (_of_fragment,
-- _of_fullFragment, _of_compact) are in Methods/EM/FragmentAdapter.lean.

end FirstOrder.Language
