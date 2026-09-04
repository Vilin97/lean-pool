/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.EM.Realization
/-!
# EM Realization: the compactness-oracle layer

The endpoints that take EM template theories from *finite satisfiability* to a model, by
applying a supplied `Theoryω.OrdinaryCompactness` oracle.

An EM template theory is built from an arbitrary
`s : ℕ → Σ n, L.BoundedFormulaω Empty n`, so its sentences lie in an arbitrary fragment: there
is no fragment-specific fact to appeal to, and no admissible module is imported here.

The oracle is genuinely an *assumption* — full `Lω₁ω` compactness for `L[[J]]` fails in
general.  `Realization.lean`'s model-input endpoints are the honest residual beneath it: they
take the model itself, and the oracle factors through them.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-! ### Stretching along an arbitrary target order

These theorems package the existing `templateTheoryOfSeq` pipeline into
caller-ready form: from an indiscernible template they produce a target
`L[[J]]`-structure `N` whose constants satisfy the template on formulas in
`Set.range s` (the countable family named by the enumeration `s`). The
target order `J` is an arbitrary linear order — including uncountable
target orders, which is where Morley–Hanf cardinality amplification lives.

Two forms are provided:

  - `stretch_restricted_of_compact` uses
    `Sentenceω.Realize (templateSentence φ t) N` as the conclusion — this is
    the form the template theory literally delivers.
  - `stretch_restricted_sequence_of_compact` produces an
    explicit `b : J → N` sequence and concludes
    `φ.Realize Empty.elim (b ∘ t) ↔ h.template.truth φ`, via the bridge
    `realize_templateSentence_of_structure`.

**Scope**: these theorems do NOT claim full `IsLomega1omegaIndiscernible` for
any extracted sequence — that would require enumerating all Lω₁ω formulas,
which is not currently formalized. They DO allow uncountable `J`, which is
what cardinality amplification for `MorleyHanfTransfer` eventually needs;
the residual step is extracting an indiscernible source sequence of length
`I ≥ ℶ_ω₁` from a large model (the Erdős–Rado half, not addressed here). -/

/-- **Generalized `realize_templateSentence`.**

Like `realize_templateSentence` (`InfinitaryLogic/Methods/EM/Realization.lean:97`),
but takes an arbitrary `[L[[J]].Structure N]` instead of requiring the
`L[[J]]`-structure to be built from a specific `σ : J → M` via
`constantsOn.structure σ`. The `L`-structure on `N` is derived from the
`L[[J]]`-structure via the canonical reduct along `lhomWithConstants L J`.

The right-hand side realizes `φ` on the sequence `fun i => b (t i)`, where
`b j` is the closed-term realization of the constant symbol `Sum.inr j`
(i.e., the interpretation of the `J`-indexed constant in the given
`L[[J]]`-structure on `N`). -/
theorem realize_templateSentence_of_structure
    {J : Type u} [LinearOrder J]
    {N : Type*} [L[[J]].Structure N]
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    letI : L.Structure N := (L.lhomWithConstants J).reduct N
    Sentenceω.Realize (Lomega1omegaTemplate.templateSentence φ t) N ↔
      φ.Realize (Empty.elim : Empty → N)
        (fun i => (Term.func (Sum.inr (t i) : L[[J]].Functions 0)
            Fin.elim0 : L[[J]].Term Empty).realize (Empty.elim : Empty → N)) := by
  let : L.Structure N := (L.lhomWithConstants J).reduct N
  have : (L.lhomWithConstants J).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  change BoundedFormulaω.Realize _ Empty.elim Fin.elim0 ↔ _
  rw [Lomega1omegaTemplate.templateSentence, BoundedFormulaω.realize_subst]
  exact (realize_openBounds _ _).trans
        (BoundedFormulaω.realize_mapLanguage _ _ _ _)

/-! ### Morley–Hanf-oriented corollaries -/

/-- The 2-ary Lω₁ω disequality formula `x₀ ≠ x₁`. -/
def disEqFormula : L.BoundedFormulaω Empty 2 :=
  (BoundedFormulaω.equal
    (Term.var (Sum.inr (0 : Fin 2)) : L.Term (Empty ⊕ Fin 2))
    (Term.var (Sum.inr (1 : Fin 2)) : L.Term (Empty ⊕ Fin 2))).not

/-- **The Morley seed** of a sentence `φ`: the concrete two-formula family the Morley–Hanf tail
bridge feeds the EM machinery — `φ` itself, the disequality `x₀ ≠ x₁`, and repeated `φ`-filler.
The honest tail-template residual quantifies over exactly this seed
(`MorleySeedTailTemplateRealizable` in `Conditional/MorleyHanfTransfer.lean`), NOT over arbitrary
formula sequences: an arbitrary sequence can enumerate `{Pᵢ x}ᵢ ∪ {⋀ᵢ Pᵢ x}` against a "height"
model, whose tail template is finitely satisfiable but unsatisfiable — a genuine `L_{ω₁ω}`
compactness failure. -/
def morleySeed (φ : L.Sentenceω) : ℕ → Σ n, L.BoundedFormulaω Empty n := fun i =>
  match i with
  | 0 => ⟨0, φ⟩
  | 1 => ⟨2, disEqFormula⟩
  | _ + 2 => ⟨0, φ⟩

/-- **The Morley seed needs no extraction**: ANY pairwise-distinct sequence is fully
`Lω₁ω`-indiscernible on `Set.range (morleySeed φ)` — the arity-`0` members ignore their tuples,
and the disequality is true on every strictly monotone pair of a pairwise-distinct sequence.
This is why the definitive Morley–Hanf route consumes no Ramsey/Erdős–Rado extraction at all:
`Infinite.natEmbedding` already supplies a seed-indiscernible sequence. -/
theorem morleySeed_indiscernibleOn {M : Type*} [L.Structure M] (φ : L.Sentenceω) {a : ℕ → M}
    (ha : ∀ i j : ℕ, i ≠ j → a i ≠ a j) :
    IsLomega1omegaIndiscernibleOn (L := L) a (Set.range (morleySeed φ)) := by
  rintro n ψ ⟨k, hk⟩ s t hs ht
  match k, hk with
  | 0, hk =>
    cases hk
    rw [show (a ∘ s : Fin 0 → M) = Fin.elim0 from funext fun p => p.elim0,
      show (a ∘ t : Fin 0 → M) = Fin.elim0 from funext fun p => p.elim0]
  | 1, hk =>
    cases hk
    exact iff_of_true
      (by
        simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
          Term.realize_var]
        intro heq
        exact ha (s 0) (s 1) (ne_of_lt (hs (show (0 : Fin 2) < 1 by decide)))
          (by simpa using heq))
      (by
        simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
          Term.realize_var]
        intro heq
        exact ha (t 0) (t 1) (ne_of_lt (ht (show (0 : Fin 2) < 1 by decide)))
          (by simpa using heq))
  | k + 2, hk =>
    cases hk
    rw [show (a ∘ s : Fin 0 → M) = Fin.elim0 from funext fun p => p.elim0,
      show (a ∘ t : Fin 0 → M) = Fin.elim0 from funext fun p => p.elim0]

/-! ### Restricted-indiscernibility variants

These `_on` theorems take `IsLomega1omegaIndiscernibleOn a (Set.range s)`
instead of the full `IsLomega1omegaIndiscernible a`, and state their
conclusions against `(templateOfSeq a).truth` rather than `h.template.truth`. -/

end FirstOrder.Language
