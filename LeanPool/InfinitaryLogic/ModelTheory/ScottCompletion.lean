/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.ArbitraryStabilization
import LeanPool.InfinitaryLogic.ModelTheory.TypePreservingBF
import LeanPool.InfinitaryLogic.Methods.UniformCollapse
import LeanPool.InfinitaryLogic.Scott.Height.CanonicalSentence
import LeanPool.InfinitaryLogic.Karp.CarrierTheorem
/-!
# The Scott completion and categoricity (issue #17 chunks 5.2–6)

The canonical Scott sentence of a countable structure — whose `scottHeight` supplies COMPLETE
STABILIZATION — characterizes its ARBITRARY models up to back-and-forth equivalence at every
ordinal (`realize_canonicalScottSentence_iff_bfEquiv_all`, via the arbitrary-target
stabilization kernel). Consequences, in order:

* any two models of the canonical sentence are pairwise `BFEquiv` at every level (transitivity
  through the countable source), hence potentially isomorphic, hence `L_∞ω`-equivalent at
  every branching carrier (`PotentialIso.infEquivAt`). `L_ω₁ω`-equivalence is then the
  carrier-`ℕ` case, not a separate result reached by an embedding: `L.Sentenceω` *is*
  `L.SentenceInf ℕ`, so `LomegaEquiv` and `InfEquivAt L ℕ` are the same proposition;
* **`Lomega1omegaComplete`** — the repository-level completeness predicate — holds for the
  canonical Scott sentence (`lomega1omegaComplete_canonicalScottSentenceω`), DERIVED from the
  semantic equivalence, never the reverse;
* **the unconditional complete-subclass intermediate**
  (`exists_complete_sentence_of_lomega1omegaSmall`): every small model of `φ` satisfies a
  complete sentence entailing `φ` — its own companion's Scott sentence;
* **the categoricity payoff** (`exists_complete_kCategorical_of_hasArbLargeModels`): if `φ`
  has arbitrarily large models and is `κ`-categorical, some complete `ψ ⊨ φ` has a model of
  size exactly `κ` and is ITSELF `κ`-categorical.

Everything is for countable relational vocabularies (`[L.IsRelational]`,
`[Countable (Σ l, L.Relations l)]`), inherited from the Scott/Karp stack per the frozen audit.
-/

namespace FirstOrder

namespace Language

open Cardinal

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
variable {N : Type} [L.Structure N] [Countable N]

/-! ## Chunk 5.2: the arbitrary-model characterization -/

/-- **Arbitrary models of the canonical Scott sentence** are back-and-forth equivalent to the
source at every ordinal — `scottHeight` supplies complete stabilization, and the
arbitrary-target kernel upgrades it. -/
private theorem realize_canonicalScottSentence_iff_bfEquiv_all {P : Type} [L.Structure P] :
    (canonicalScottSentence (L := L) N).realizeAsSentence P ↔
      ∀ β : Ordinal.{0},
        BFEquiv (L := L) β 0 (Fin.elim0 : Fin 0 → N) (Fin.elim0 : Fin 0 → P) := by
  unfold canonicalScottSentence Formulaω.realizeAsSentence
  rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1 N)]
  constructor
  · intro h β
    exact bfEquiv_all_of_stabilizesCompletely_arbitrary
      (scottHeight_lt_omega1 N) (scottHeight_stabilizesCompletely N) h β
  · intro h
    exact h _

/-- The canonical Scott sentence in `Sentenceω` form. -/
private noncomputable def canonicalScottSentenceω (N : Type) [L.Structure N] [Countable N] :
    L.Sentenceω :=
  (canonicalScottSentence (L := L) N).relabel (Sum.inr : Fin 0 → Empty ⊕ Fin 0)

omit [L.IsRelational] in
private theorem realize_canonicalScottSentenceω_iff {P : Type} [L.Structure P] :
    Sentenceω.Realize (canonicalScottSentenceω (L := L) N) P ↔
      (canonicalScottSentence (L := L) N).realizeAsSentence P := by
  have h := BoundedFormulaω.realize_relabel_sumInr (M := P)
    (φ := (canonicalScottSentence (L := L) N : L.BoundedFormulaω (Fin 0) 0))
    (xs := (Fin.elim0 : Fin 0 → P))
  rwa [show ((Fin.elim0 : Fin 0 → P) ∘ Fin.castAdd 0 : Fin 0 → P) = Fin.elim0 from
      funext fun i => i.elim0,
    show ((Fin.elim0 : Fin 0 → P) ∘ Fin.natAdd 0 : Fin 0 → P) = Fin.elim0 from
      funext fun i => i.elim0] at h

private theorem realize_canonicalScottSentenceω_iff_bfEquiv_all {P : Type} [L.Structure P] :
    Sentenceω.Realize (canonicalScottSentenceω (L := L) N) P ↔
      ∀ β : Ordinal.{0},
        BFEquiv (L := L) β 0 (Fin.elim0 : Fin 0 → N) (Fin.elim0 : Fin 0 → P) :=
  realize_canonicalScottSentenceω_iff.trans realize_canonicalScottSentence_iff_bfEquiv_all

/-- The source satisfies its own canonical Scott sentence. -/
private theorem realize_canonicalScottSentenceω_self :
    Sentenceω.Realize (canonicalScottSentenceω (L := L) N) N :=
  realize_canonicalScottSentenceω_iff_bfEquiv_all.mpr fun β =>
    BFEquiv.refl (L := L) β (Fin.elim0 : Fin 0 → N)

/-! ## Chunk 5.3: semantic completeness first, syntactic completeness after -/

/-- **Pairwise equivalence**: any two models of the canonical Scott sentence are back-and-forth
equivalent at every ordinal, by transitivity through the countable source. -/
private theorem bfEquiv_all_of_realize_canonicalScottSentenceω_pair {P Q : Type}
    [L.Structure P] [L.Structure Q]
    (hP : Sentenceω.Realize (canonicalScottSentenceω (L := L) N) P)
    (hQ : Sentenceω.Realize (canonicalScottSentenceω (L := L) N) Q) (β : Ordinal.{0}) :
    BFEquiv (L := L) β 0 (Fin.elim0 : Fin 0 → P) (Fin.elim0 : Fin 0 → Q) :=
  BFEquiv.trans
    (BFEquiv.symm (realize_canonicalScottSentenceω_iff_bfEquiv_all.mp hP β))
    (realize_canonicalScottSentenceω_iff_bfEquiv_all.mp hQ β)

/-- **Semantic `L_∞ω`-completeness**: any two models of the canonical Scott sentence are
`L_∞ω`-equivalent, at every branching carrier. -/
private theorem infEquivW_of_realize_canonicalScottSentenceω_pair {P Q : Type}
    [L.Structure P] [L.Structure Q]
    (hP : Sentenceω.Realize (canonicalScottSentenceω (L := L) N) P)
    (hQ : Sentenceω.Realize (canonicalScottSentenceω (L := L) N) Q) :
    InfEquivW L P Q := by
  obtain ⟨pi⟩ := BFEquiv_all_implies_potentialIso
    (bfEquiv_all_of_realize_canonicalScottSentenceω_pair hP hQ)
  exact fun ι => pi.infEquivAt ι

/-- `L_ω₁ω`-equivalence of any two models: the carrier-`ℕ` case of the previous theorem.

There is no embedding step. `L.Sentenceω` *is* `L.SentenceInf ℕ`, and `LomegaEquiv L P Q` is
`InfEquivAt L ℕ P Q` — the same proposition, accepted by `rfl` — so specializing the carrier
is the whole proof. -/
private theorem lomegaEquiv_of_realize_canonicalScottSentenceω_pair {P Q : Type}
    [L.Structure P] [L.Structure Q]
    (hP : Sentenceω.Realize (canonicalScottSentenceω (L := L) N) P)
    (hQ : Sentenceω.Realize (canonicalScottSentenceω (L := L) N) Q) :
    LomegaEquiv L P Q :=
  infEquivW_of_realize_canonicalScottSentenceω_pair hP hQ ℕ

/-- **Repository-level completeness**: a sentence is `L_ω₁ω`-complete when it decides every
`Sentenceω` across its models. -/
def Lomega1omegaComplete (ψ : L.Sentenceω) : Prop :=
  ∀ φ : L.Sentenceω,
    (∀ (P : Type) (_ : L.Structure P), Sentenceω.Realize ψ P → Sentenceω.Realize φ P) ∨
    (∀ (P : Type) (_ : L.Structure P), Sentenceω.Realize ψ P → ¬Sentenceω.Realize φ P)

/-- **The canonical Scott sentence is complete** — derived from the semantic equivalence of
its models, anchored at the source. -/
private theorem lomega1omegaComplete_canonicalScottSentenceω :
    Lomega1omegaComplete (canonicalScottSentenceω (L := L) N) := by
  intro φ
  by_cases hN : Sentenceω.Realize φ N
  · exact Or.inl fun P _ hP =>
      (lomegaEquiv_of_realize_canonicalScottSentenceω_pair
        realize_canonicalScottSentenceω_self hP φ).mp hN
  · exact Or.inr fun P _ hP hφP => hN
      ((lomegaEquiv_of_realize_canonicalScottSentenceω_pair
        realize_canonicalScottSentenceω_self hP φ).mpr hφP)

/-- **Entailment**: the canonical Scott sentence entails every sentence its source satisfies. -/
private theorem canonicalScottSentenceω_entails {φ : L.Sentenceω}
    (hφ : Sentenceω.Realize φ N) {P : Type} [L.Structure P]
    (hP : Sentenceω.Realize (canonicalScottSentenceω (L := L) N) P) :
    Sentenceω.Realize φ P :=
  (lomegaEquiv_of_realize_canonicalScottSentenceω_pair
    realize_canonicalScottSentenceω_self hP φ).mp hφ

/-- **The unconditional complete-subclass intermediate** (issue #17 chunk 5 endpoint): every
small model of `φ` satisfies a complete sentence entailing `φ` — its own countable companion's
canonical Scott sentence. -/
theorem exists_complete_sentence_of_lomega1omegaSmall {M : Type} [L.Structure M]
    (hsmall : Lomega1omegaSmall (L := L) M) {φ : L.Sentenceω}
    (hφ : Sentenceω.Realize φ M) :
    ∃ ψ : L.Sentenceω, Lomega1omegaComplete ψ ∧ Sentenceω.Realize ψ M ∧
      ∀ (P : Type) (_ : L.Structure P), Sentenceω.Realize ψ P → Sentenceω.Realize φ P := by
  have : Countable (Σ n, L.Functions n) := countable_functions_of_isRelational
  obtain ⟨N', hcnt, hAe⟩ := exists_countable_companion hsmall
  refine ⟨canonicalScottSentenceω (L := L) N', lomega1omegaComplete_canonicalScottSentenceω,
    ?_, ?_⟩
  · -- M models the companion's Scott sentence: BFEquiv-all M–N' from chunk 4, symmetrized
    exact realize_canonicalScottSentenceω_iff_bfEquiv_all.mpr fun β =>
      BFEquiv.symm (bfEquiv_all_of_companion hAe β)
  · -- entailment: the companion satisfies φ (transfer along the same equivalence)
    intro P _ hP
    refine canonicalScottSentenceω_entails ?_ hP
    have hMψ : Sentenceω.Realize (canonicalScottSentenceω (L := L) N') M :=
      realize_canonicalScottSentenceω_iff_bfEquiv_all.mpr fun β =>
        BFEquiv.symm (bfEquiv_all_of_companion hAe β)
    exact (lomegaEquiv_of_realize_canonicalScottSentenceω_pair
      realize_canonicalScottSentenceω_self hMψ φ).mpr hφ

/-! ## Chunk 6: the categoricity payoff -/

/-- `κ`-categoricity of a sentence: all `κ`-sized models are isomorphic. -/
def KCategorical (φ : L.Sentenceω) (κ : Cardinal.{0}) : Prop :=
  ∀ (P Q : Type) (_ : L.Structure P) (_ : L.Structure Q),
    Sentenceω.Realize φ P → Sentenceω.Realize φ Q →
    Cardinal.mk P = κ → Cardinal.mk Q = κ → Nonempty (P ≃[L] Q)

/-- **The categoricity payoff** (issue #17 chunk 6): a `κ`-categorical sentence with
arbitrarily large models admits a COMPLETE sentence entailing it, with a model of size exactly
`κ` — and the complete sentence is itself `κ`-categorical. -/
theorem exists_complete_kCategorical_of_hasArbLargeModels {φ : L.Sentenceω}
    (hφarb : HasArbLargeModels φ) {κ : Cardinal.{0}} (hκ : Cardinal.aleph0 ≤ κ)
    (hcat : KCategorical φ κ) :
    ∃ ψ : L.Sentenceω, Lomega1omegaComplete ψ ∧
      (∀ (P : Type) (_ : L.Structure P), Sentenceω.Realize ψ P → Sentenceω.Realize φ P) ∧
      (∃ (P : Type) (_ : L.Structure P), Sentenceω.Realize ψ P ∧ Cardinal.mk P = κ) ∧
      KCategorical ψ κ := by
  have : Countable (Σ n, L.Functions n) := countable_functions_of_isRelational
  obtain ⟨M, instM, hφM, hMκ, hsmall⟩ := exists_small_model_of_hasArbLargeModels hφarb hκ
  obtain ⟨ψ, hcomp, hψM, hent⟩ := exists_complete_sentence_of_lomega1omegaSmall hsmall hφM
  refine ⟨ψ, hcomp, hent, ⟨M, instM, hψM, hMκ⟩, ?_⟩
  intro P Q instP instQ hP hQ hPκ hQκ
  exact hcat P Q instP instQ (hent P instP hP) (hent Q instQ hQ) hPκ hQκ

end Language

end FirstOrder
