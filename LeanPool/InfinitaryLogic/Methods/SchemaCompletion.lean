/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.SchemaOmegaWitness
import LeanPool.InfinitaryLogic.Methods.LanguageMapOccurrence
import LeanPool.InfinitaryLogic.Methods.MarkerStage
/-!
# Layer 7b, checkpoint 1: the countable schema sentence universe

The ω-stage Henkin/template completion (Layer 7) is carried out at the **schema level**, over
the canonical countable index `J := ℕ` (the indiscernible-sequence positions `d₀, d₁, …`), where
the sentence set the completion ranges over is genuinely countable — unlike the uncountable
`L'[[J]]`-constant instances for arbitrary `J` that defeated the Layer-6c Zorn maximal.

This file fixes the **schema sentence universe**: the set of `(localColim s₀)[[ℕ]]`-sentences the
enumeration in checkpoint 3 will decide. A crucial simplification, established in
`SchemaOmegaWitness`, drives the shape: the target witness property
`TailTemplateOmegaWitnessed`/`OmegaCompleteForColim` has **only `iSup`/`iInf` clauses, no
existential** (the local-EM de-substituted formulas are already Skolemized). Since `ΓlocalColim`
— hence `ΓEMlocal` — is closed under `iSup`/`iInf` components
(`iSup_component_mem_ΓlocalColim`), every disjunct a completion might choose as a witness is
**already** a member of the seed family. So the universe is exactly the `templateSentence`
instantiations of the `ΓEMlocal` members at `ℕ`-tuples:

* the seed family `ΓEMlocal s₀` is **countable** (`ΓEMlocal_countable`);
* for each member `⟨m, φ⟩`, the increasing `ℕ`-tuples `t : Fin m ↪o ℕ` form a **countable** type
  (they inject into `Fin m → ℕ`);
* `templateSentence φ t` is the `L[[ℕ]]`-sentence "`φ` holds on `d_{t 0}, …, d_{t (m-1)}`".

`schemaSentenceUniverse_countable` is the checkpoint-1 payoff (the completion's decision list is
enumerable); `schemaSentenceUniverse_nonempty` supplies the base point the enumeration needs.
No completion, Zorn, term model, or `realizeWith` bridge appears here — this checkpoint only
pins the countable substrate.
-/

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage}

/-- Increasing `ℕ`-tuples of any fixed length are countable: the coercion to `Fin m → ℕ` is
injective, and `Fin m → ℕ` is countable. -/
instance instCountableFinOrderEmbNat (m : ℕ) : Countable (Fin m ↪o ℕ) :=
  (DFunLike.coe_injective (F := Fin m ↪o ℕ) (α := Fin m) (β := fun _ => ℕ)).countable

/-- **The schema sentence universe.** Over the base language `(localColim s₀)[[ℕ]]` (`ℕ` the
canonical indiscernible-sequence positions), the set of `templateSentence φ t` — "`φ` holds on
the constants `d_{t 0}, …, d_{t (m-1)}`" — as `⟨m, φ⟩` ranges over the colimit atom/connective
family `ΓEMlocal s₀` and `t` over the increasing `ℕ`-tuples of length `m`. This is the countable
decision list of the ω-stage completion; its `iSup`/`iInf` witnesses stay inside it because
`ΓEMlocal ⊇ ΓlocalColim` is component-closed. -/
def schemaSentenceUniverse (s₀ : LocalStage) : Set ((localColim s₀)[[ℕ]].Sentenceω) :=
  ⋃ (mφ ∈ ΓEMlocal s₀), Set.range fun t : Fin mφ.1 ↪o ℕ =>
    Lomega1omegaTemplate.templateSentence mφ.2 t

/-- **Checkpoint 1.** The schema sentence universe is countable — a countable union (over the
countable seed family `ΓEMlocal s₀`) of ranges of maps out of the countable tuple types. This is
what makes the ω-enumeration of the completion possible. -/
theorem schemaSentenceUniverse_countable : (schemaSentenceUniverse s₀).Countable :=
  (ΓEMlocal_countable s₀).biUnion fun _ _ => Set.countable_range _

/-- A canonical length-`m` increasing `ℕ`-tuple: the inclusion `Fin m ↪ ℕ` by value, which is
strictly monotone. Used to base-point the schema universe. -/
def stdTuple (m : ℕ) : Fin m ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun i => (i : ℕ)) fun _ _ h => h

/-- The schema sentence universe is nonempty: the seed family is nonempty
(`ΓEMlocal_nonempty`) and every arity admits the standard tuple, so the corresponding
`templateSentence` is a member. Supplies the base point the enumeration in checkpoint 3 needs. -/
theorem schemaSentenceUniverse_nonempty : (schemaSentenceUniverse s₀).Nonempty := by
  obtain ⟨mφ, hmφ⟩ := ΓEMlocal_nonempty s₀
  exact ⟨Lomega1omegaTemplate.templateSentence mφ.2 (stdTuple mφ.1),
    Set.mem_biUnion hmφ ⟨stdTuple mφ.1, rfl⟩⟩

/-! ## Checkpoint 2, step 1: the template-realization bridge

Connects MarkerStage's `realizeWith` (over the double Henkin expansion `((L''[[J]])[[ℕ]])`) to the
`templateSentence` semantics: the schema sentence `templateSentence ψ t`, lifted into the Marker
language along the Henkin inclusion, is `realizeWith`-true under a skeleton interpretation `σ`
exactly when `ψ` holds on the `σ`-images `i ↦ σ (t i)` of its constants. The Henkin layer is inert
(no Henkin constants occur). This is the semantic content the base certification (step 3) and the
seed agreement (7c) both consume. Stated generically in `L''`/`J`, so the two `constantsOn`
instances of `realizeWith` stay unambiguous (as at its definition site). -/

section TemplateBridge

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J] {M : Type} [L''.Structure M]

/-- **The template-realization bridge.** `templateSentence ψ t` (over `L''[[J]]`), lifted into the
Marker double expansion `((L''[[J]])[[ℕ]])` along the Henkin inclusion, realizes under a skeleton
interpretation `σ : J → M` and any Henkin interpretation `h : ℕ → M` iff `ψ` holds on the tuple
`i ↦ σ (t i)`. Composes `sentenceRealize_iff_realizeWith`, `realize_mapLanguage` (the Henkin
inclusion is an expansion, `withConstants_expansion`), and the existing `realize_templateSentence`. -/
theorem realizeWith_templateSentence (σ : J → M) (h : ℕ → M)
    {n : ℕ} (ψ : L''.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    realizeWith σ h
        ((Lomega1omegaTemplate.templateSentence ψ t).mapLanguage
          ((L''[[J]]).lhomWithConstants ℕ))
        (Empty.elim : Empty → M) Fin.elim0
      ↔ ψ.Realize (Empty.elim : Empty → M) (fun i => σ (t i)) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  let : (constantsOn ℕ).Structure M := constantsOn.structure h
  rw [← sentenceRealize_iff_realizeWith]
  show Sentenceω.Realize _ M ↔ _
  rw [Sentenceω.realize_def]
  rw [BoundedFormulaω.realize_mapLanguage ((L''[[J]]).lhomWithConstants ℕ)
    (Lomega1omegaTemplate.templateSentence ψ t)]
  exact realize_templateSentence σ ψ t

end TemplateBridge

/-! ## Checkpoint 2: the empty base is Marker-consistent

The ω-stage completion (checkpoint 3) starts from the empty theory and decides every schema
sentence's sign via the already-proved `MarkerHenkinConsistent.extension` (which internally
homogenizes through `markerStage_homogeneous`). Since `schemaSentenceUniverse` is a *decision
list* — its canonical atoms include both true and false instances (e.g. `x₀ = x₁`) — the base is
NOT "all universe sentences are true"; it is the trivially-realizable empty fragment. The Morley
seed `{φ, x₀ ≠ x₁}` needs no explicit seeding: `extension` is forced to pick `φ` (its negation is
incompatible with `M ⊨ φ`) and distinctness (its negation is incompatible with the strictly
increasing skeleton interpretations). -/

section EmptyBase

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J]
  {M : Type} [L''.Structure M] [LinearOrder M] [WellFoundedLT M]

/-- **Checkpoint 2.** The empty fragment is `MarkerHenkinConsistent M` for any source `M` of size
`≥ ℶ_ω₁`: at every level `β < ω₁` the body is the trivial certificate over the `(ℶ_β)⁺`-suborder
`e` supplied by `markerStage_homogeneous` at empty arity, with no members to realize. This is the
starting point the ω-stage `extension`/`iSup_choice` chain builds on. -/
theorem markerHenkinConsistent_empty
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    MarkerHenkinConsistent M (∅ : Finset (((L''[[J]])[[ℕ]]).Sentenceω)) := by
  have : Nonempty M := Cardinal.mk_ne_zero_iff.mp
    (((lt_of_lt_of_le Cardinal.aleph0_pos (Cardinal.aleph0_le_beth _)).trans_le hM).ne')
  refine ⟨∅, ∅, fun τ hτ => by simp at hτ, fun τ hτ => by simp at hτ, fun β hβ => ?_⟩
  obtain ⟨_, _, _, _, _, e, _⟩ :=
    markerStage_homogeneous (L' := L'') M hM β hβ (J := J)
      (m := 0) (ar := Fin.elim0) (fun p => p.elim0) (fun p => p.elim0)
  exact ⟨β, le_refl β, hβ, e, fun σ _ _ => ⟨fun _ => Classical.arbitrary M, fun τ hτ => by simp at hτ⟩⟩

end EmptyBase

/-! ## Checkpoint 3a: the lifted universe and its `FSentence` membership

The ω-stage completion runs over `((localColim s₀)[[ℕ]])[[ℕ]]` (`FSentence`), so the universe must
be lifted along the same Henkin inclusion as the bridge. Two `functionsIn`-under-`mapLanguage`
facts (absent from the existing `relabel`/`subst`/`openBounds` API) drive the constant-support
computation: lifting sends every function symbol to its `Sum.inl` image, so it produces **no**
Henkin constants and preserves the skeleton-constant support. A lifted `templateSentence ψ t` then
has finite constant support `image t` (and empty Henkin support) — regardless of how many base
function symbols the (possibly `iSup`-branching) `ψ` uses, because `HasFiniteConstSupport` bounds
only the *constant* symbols, never all of `functionsIn`. -/

section FunctionsInMapLanguage

variable {L L' : Language.{0, 0}} (g : L →ᴸ L')


end FunctionsInMapLanguage

section HenkinLiftSupport

variable {L'' : Language.{0, 0}} {J : Type}

/-- The Henkin inclusion `(L''[[J]]) →ᴸ ((L''[[J]])[[ℕ]])` sends every function symbol to its
`Sum.inl` image; hence a lifted formula has **no** Henkin constants. -/
theorem henkinConstsIn_mapLanguage {α : Type} {n : ℕ} (τ : (L''[[J]]).BoundedFormulaω α n) :
    henkinConstsIn (L'' := L'') (τ.mapLanguage ((L''[[J]]).lhomWithConstants ℕ)) = ∅ := by
  ext m
  simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
    BoundedFormulaω.functionsIn_mapLanguage, Set.mem_image, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  rintro ⟨k, f⟩ _ heq
  -- `rw [Sigma.mk.injEq]` / `rw [heq_eq_eq]` no longer fire: the sigma payload spells the symbol
  -- at its whnf'd sum type, so the equation is not type-correct at `implicit` transparency.
  obtain ⟨rfl, heq2⟩ := Sigma.mk.inj_iff.mp heq
  have heq3 : ((L''[[J]]).lhomWithConstants ℕ).onFunction f = Sum.inr m := eq_of_heq heq2
  simp at heq3

/-- The Henkin inclusion preserves the skeleton (`J`) constant support: the expansion `J`-constants
of a lifted formula are exactly the `J`-constants of the original. -/
theorem expJConstsIn_mapLanguage {α : Type} {n : ℕ} (τ : (L''[[J]]).BoundedFormulaω α n) :
    expJConstsIn (L'' := L'') (τ.mapLanguage ((L''[[J]]).lhomWithConstants ℕ)) =
      sentenceJConsts (L' := L'') (J := J) τ := by
  ext j
  simp only [expJConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
    BoundedFormulaω.functionsIn_mapLanguage, Set.mem_image]
  constructor
  · rintro ⟨⟨k, f⟩, hf, heq⟩
    obtain ⟨rfl, heq2⟩ := Sigma.mk.inj_iff.mp heq
    have heq3 : ((L''[[J]]).lhomWithConstants ℕ).onFunction f = Sum.inl (Sum.inr j) :=
      eq_of_heq heq2
    have hf2 : f = Sum.inr j := Sum.inl_injective heq3
    exact hf2 ▸ hf
  · intro hj
    exact ⟨⟨0, Sum.inr j⟩, hj, rfl⟩

end HenkinLiftSupport

section TemplateSupport

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J]

/-- The only `J`-constants of a `templateSentence ψ t` are the tuple's constants: substitution
introduces exactly `{t 0, …, t (n-1)}` and the `mapLanguage`d body contributes only base
(`Sum.inl`) symbols. -/
theorem sentenceJConsts_templateSentence {n : ℕ} (ψ : L''.BoundedFormulaω Empty n)
    (t : Fin n ↪o J) :
    sentenceJConsts (L' := L'') (J := J) (Lomega1omegaTemplate.templateSentence ψ t)
      ⊆ Set.range (⇑t) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_ofPred_eq, Lomega1omegaTemplate.templateSentence] at hj
  have hsub := BoundedFormulaω.functionsIn_subst
    (fun i => Term.func (Sum.inr (t i) : (L''[[J]]).Functions 0) Fin.elim0)
    ((ψ.mapLanguage (L''.lhomWithConstants J)).openBounds) hj
  rw [BoundedFormulaω.functionsIn_openBounds] at hsub
  rcases hsub with hbody | hconst
  · rw [BoundedFormulaω.functionsIn_mapLanguage] at hbody
    obtain ⟨⟨k, f⟩, -, heq⟩ := hbody
    obtain ⟨rfl, heq2⟩ := Sigma.mk.inj_iff.mp heq
    have heq3 : (L''.lhomWithConstants J).onFunction f = Sum.inr j := eq_of_heq heq2
    exact absurd heq3 (by simp)
  · simp only [Set.mem_iUnion, Term.functionsIn, Set.iUnion_of_empty,
      Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hconst
    obtain ⟨i, hi⟩ := hconst
    obtain ⟨-, hi2⟩ := Sigma.mk.inj_iff.mp hi
    have hi3 : (Sum.inr j : (L''[[J]]).Functions 0) = Sum.inr (t i) := eq_of_heq hi2
    exact ⟨i, (Sum.inr_injective hi3).symm⟩

/-- **Every lifted `templateSentence` is an `FSentence`.** Its expansion `J`-support is the finite
tuple image `image t`, and its Henkin support is empty. -/
theorem hasFiniteConstSupport_mapLanguage_templateSentence {n : ℕ}
    (ψ : L''.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    HasFiniteConstSupport (L'' := L'')
      ((Lomega1omegaTemplate.templateSentence ψ t).mapLanguage
        ((L''[[J]]).lhomWithConstants ℕ)) := by
  refine ⟨Finset.image (⇑t) Finset.univ, ∅, ?_, ?_⟩
  · rw [expJConstsIn_mapLanguage]
    intro j hj
    obtain ⟨i, hi⟩ := sentenceJConsts_templateSentence ψ t hj
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  · rw [henkinConstsIn_mapLanguage]; exact Set.empty_subset _

end TemplateSupport

section LiftedUniverse

variable {s₀ : LocalStage}

/-- **The lifted schema universe**, as a set of `FSentence`s over the Marker language
`((localColim s₀)[[ℕ]])[[ℕ]]`: each schema sentence `templateSentence ψ t` (`⟨m, ψ⟩ ∈ ΓEMlocal`),
lifted along the Henkin inclusion and packaged with its finite-support proof. This is the
enumeration domain the ω-stage completion (checkpoint 3b) decides. -/
def schemaFSentenceUniverse (s₀ : LocalStage) :
    Set (FSentence (L'' := localColim s₀) (J := ℕ)) :=
  ⋃ (mφ ∈ ΓEMlocal s₀), Set.range fun t : Fin mφ.1 ↪o ℕ =>
    (⟨(Lomega1omegaTemplate.templateSentence mφ.2 t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ),
      hasFiniteConstSupport_mapLanguage_templateSentence mφ.2 t⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ))

/-- **Checkpoint 3a.** The lifted schema `FSentence` universe is countable — the enumeration the
completion needs exists. -/
theorem schemaFSentenceUniverse_countable : (schemaFSentenceUniverse s₀).Countable :=
  (ΓEMlocal_countable s₀).biUnion fun _ _ => Set.countable_range _

/-- The lifted schema `FSentence` universe is nonempty (base point for the enumeration). -/
theorem schemaFSentenceUniverse_nonempty : (schemaFSentenceUniverse s₀).Nonempty := by
  obtain ⟨mφ, hmφ⟩ := ΓEMlocal_nonempty s₀
  exact ⟨_, Set.mem_biUnion hmφ ⟨stdTuple mφ.1, rfl⟩⟩

end LiftedUniverse

/-! ## Checkpoint 3b: the ω-stage completion (subtype recursion)

A constructive Henkin enumeration over `ρ : ℕ → FSentence`. Each `stageStep` decides `ρ n` via
`extension` (branching on decidable consistency of the positive insert — `extension`'s `∨` is a
`Prop` and cannot eliminate into the `Subtype`), and, opportunistically and locally, adjoins the
connective witness of the decided sign: a positive `iSup` gets a disjunct via `iSup_choice`, a
negative `iInf` gets a refuted conjunct via `neg_iInf_choice`. The step carries the balanced
disjunction `(positive ∧ iSup-witnessed) ∨ (negative ∧ neg-iInf-witnessed)`, so the per-stage
facts 3c consumes are projections — no global classifier, no "φ ∉ F" discharge. The negative
witness is NOT recoverable from finite consistency after the theory is formed (a finite
fragment's body can falsify a component the fragment does not mention, so the failing component
drifts with the body); it must be pinned here, at decision time. -/

section Completion

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (ρ : ℕ → FSentence (L'' := localColim s₀) (J := ℕ))

/-- **The stage step.** Given a consistent finite stage `Fp`, decide `ρ n` and (locally) witness
the decided sign's connective: a positive `iSup` gets a disjunct, a negative `iInf` a refuted
conjunct. Returns the next stage with consistency, monotonicity, and the balanced decision record
`(positive ∧ iSup-witnessed) ∨ (negative ∧ neg-iInf-witnessed)`. -/
noncomputable def stageStep
    (Fp : {F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) // MarkerHenkinConsistent M F})
    (n : ℕ) :
    {G : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) //
      MarkerHenkinConsistent M G ∧ Fp.1 ⊆ G ∧
      (((ρ n).1 ∈ G ∧ ∀ φs, (ρ n).1 = BoundedFormulaω.iSup φs → ∃ k, φs k ∈ G) ∨
        ((ρ n).1.not ∈ G ∧
          ∀ φs, (ρ n).1 = BoundedFormulaω.iInf φs → ∃ k, (φs k).not ∈ G))} := by
  classical
  by_cases hpos : MarkerHenkinConsistent M (insert (ρ n).1 Fp.1)
  · by_cases hSup : ∃ φs, (ρ n).1 = BoundedFormulaω.iSup φs
    · have hφs : (ρ n).1 = BoundedFormulaω.iSup (Classical.choose hSup) :=
        Classical.choose_spec hSup
      have hmem : BoundedFormulaω.iSup (Classical.choose hSup) ∈ insert (ρ n).1 Fp.1 :=
        hφs ▸ Finset.mem_insert_self _ _
      have hk := Classical.choose_spec (MarkerHenkinConsistent.iSup_choice hpos hmem)
      set k := Classical.choose (MarkerHenkinConsistent.iSup_choice hpos hmem)
      refine ⟨insert (Classical.choose hSup k) (insert (ρ n).1 Fp.1), hk,
        (Finset.subset_insert _ _).trans (Finset.subset_insert _ _),
        Or.inl ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun φs' hφs' => ?_⟩⟩
      have hφeq : Classical.choose hSup = φs' := by
        have h := hφs.symm.trans hφs'
        rwa [BoundedFormulaInf.iSup.injEq] at h
      exact ⟨k, by rw [← congrFun hφeq k]; exact Finset.mem_insert_self _ _⟩
    · refine ⟨insert (ρ n).1 Fp.1, hpos, Finset.subset_insert _ _,
        Or.inl ⟨Finset.mem_insert_self _ _, fun φs' hφs' => ?_⟩⟩
      exact absurd ⟨φs', hφs'⟩ hSup
  · have hneg := (MarkerHenkinConsistent.extension Fp.2 (ρ n).1 (ρ n).2).resolve_left hpos
    by_cases hInf : ∃ φs, (ρ n).1 = BoundedFormulaω.iInf φs
    · have hφs : (ρ n).1 = BoundedFormulaω.iInf (Classical.choose hInf) :=
        Classical.choose_spec hInf
      have hmem : (BoundedFormulaω.iInf (Classical.choose hInf)).not ∈
          insert (ρ n).1.not Fp.1 := by
        rw [← hφs]; exact Finset.mem_insert_self _ _
      have hk := Classical.choose_spec (MarkerHenkinConsistent.neg_iInf_choice hneg hmem)
      set k := Classical.choose (MarkerHenkinConsistent.neg_iInf_choice hneg hmem)
      refine ⟨insert (Classical.choose hInf k).not (insert (ρ n).1.not Fp.1), hk,
        (Finset.subset_insert _ _).trans (Finset.subset_insert _ _),
        Or.inr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun φs' hφs' => ?_⟩⟩
      have hφeq : Classical.choose hInf = φs' := by
        have h := hφs.symm.trans hφs'
        rwa [BoundedFormulaInf.iInf.injEq] at h
      exact ⟨k, by rw [← congrFun hφeq k]; exact Finset.mem_insert_self _ _⟩
    · refine ⟨insert (ρ n).1.not Fp.1, hneg, Finset.subset_insert _ _,
        Or.inr ⟨Finset.mem_insert_self _ _, fun φs' hφs' => ?_⟩⟩
      exact absurd ⟨φs', hφs'⟩ hInf

/-- **The completion stages.** `T 0 = ∅`; `T (n+1)` is the `stageStep` of `T n`. -/
noncomputable def schemaCompletionStage
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    ℕ → {F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) // MarkerHenkinConsistent M F}
  | 0 => ⟨∅, markerHenkinConsistent_empty hM⟩
  | n + 1 =>
    ⟨(stageStep ρ (schemaCompletionStage hM n) n).1,
      (stageStep ρ (schemaCompletionStage hM n) n).2.1⟩

omit [WellFoundedLT M] in
/-- **`C0` at the consistency level**: a `MarkerHenkinConsistent` fragment contains no sentence
together with its negation (a body at some level realizes both, contradicting `realizeWith_not`). -/
theorem markerHenkinConsistent_not_mem_and_not_mem
    {F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    (τ : ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) : ¬(τ ∈ F ∧ τ.not ∈ F) := by
  rintro ⟨h1, h2⟩
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  obtain ⟨α, -, -, e, hsat⟩ := hcof 0 (Ordinal.omega_pos 1)
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  obtain ⟨hval, hh⟩ := hsat σ hmono hrange
  exact (realizeWith_not σ hval τ _ _).mp
    (hh τ.not (Finset.mem_coe.mpr h2)) (hh τ (Finset.mem_coe.mpr h1))

variable (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- Each stage is `MarkerHenkinConsistent` (built into the subtype). -/
theorem schemaCompletionStage_consistent (n : ℕ) :
    MarkerHenkinConsistent M (schemaCompletionStage ρ hM n).1 :=
  (schemaCompletionStage ρ hM n).2

/-- One-step monotonicity: a stage is contained in its successor. -/
theorem schemaCompletionStage_subset_succ (n : ℕ) :
    (schemaCompletionStage ρ hM n).1 ⊆ (schemaCompletionStage ρ hM (n + 1)).1 :=
  (stageStep ρ (schemaCompletionStage ρ hM n) n).2.2.1

/-- Monotonicity of the completion chain. -/
theorem schemaCompletionStage_mono {m n : ℕ} (h : m ≤ n) :
    (schemaCompletionStage ρ hM m).1 ⊆ (schemaCompletionStage ρ hM n).1 := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (schemaCompletionStage_subset_succ ρ hM n)
    · exact subset_rfl

/-- **Stage `n` decides `ρ n`**: after stage `n+1`, either `(ρ n).1` or its negation is present. -/
theorem schemaCompletionStage_decides (n : ℕ) :
    (ρ n).1 ∈ (schemaCompletionStage ρ hM (n + 1)).1 ∨
      (ρ n).1.not ∈ (schemaCompletionStage ρ hM (n + 1)).1 := by
  rcases (stageStep ρ (schemaCompletionStage ρ hM n) n).2.2.2 with ⟨hmem, -⟩ | ⟨hneg, -⟩
  · exact Or.inl hmem
  · exact Or.inr hneg

/-- **Stage `n` witnesses a positive `iSup`**: if `(ρ n).1` is `iSup φs` and lands positively in
stage `n+1`, some component `φs k` is present too. -/
theorem schemaCompletionStage_witness (n : ℕ) {φs : ℕ → ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω}
    (hiSup : (ρ n).1 = BoundedFormulaω.iSup φs)
    (hpos : (ρ n).1 ∈ (schemaCompletionStage ρ hM (n + 1)).1) :
    ∃ k, φs k ∈ (schemaCompletionStage ρ hM (n + 1)).1 := by
  rcases (stageStep ρ (schemaCompletionStage ρ hM n) n).2.2.2 with ⟨-, hwit⟩ | ⟨hneg, -⟩
  · exact hwit φs hiSup
  · exact absurd ⟨hpos, hneg⟩
      (markerHenkinConsistent_not_mem_and_not_mem
        (schemaCompletionStage_consistent ρ hM (n + 1)) (ρ n).1)

/-- **Stage `n` witnesses a negative `iInf`**: if `(ρ n).1` is `iInf φs` and its negation lands in
stage `n+1`, some refuted component `(φs k).not` is present too. The mirror of
`schemaCompletionStage_witness`, projecting the negative half of the balanced decision record. -/
theorem schemaCompletionStage_neg_iInf_witness (n : ℕ)
    {φs : ℕ → ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω}
    (hiInf : (ρ n).1 = BoundedFormulaω.iInf φs)
    (hneg : (ρ n).1.not ∈ (schemaCompletionStage ρ hM (n + 1)).1) :
    ∃ k, (φs k).not ∈ (schemaCompletionStage ρ hM (n + 1)).1 := by
  rcases (stageStep ρ (schemaCompletionStage ρ hM n) n).2.2.2 with ⟨hpos, -⟩ | ⟨-, hwit⟩
  · exact absurd ⟨hpos, hneg⟩
      (markerHenkinConsistent_not_mem_and_not_mem
        (schemaCompletionStage_consistent ρ hM (n + 1)) (ρ n).1)
  · exact hwit φs hiInf

end Completion

/-! ## Checkpoint 3c: the union theory

The completed theory `T = ⋃ₙ (schemaCompletionStage ρ hM n).1`, kept as a raw set of Marker
sentences. Finite-character consistency (a finite subset lands in one stage), completeness on the
universe (each `ρ n` decided at its stage), and — the `iSup`-witness closure — will bundle into
`SchemaCompletionTheorySpec`. -/

section Union

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M]

/-- **The canonical enumeration** of the schema universe (from countable + nonempty). -/
noncomputable def schemaEnumeration (s₀ : LocalStage) :
    ℕ → FSentence (L'' := localColim s₀) (J := ℕ) :=
  ((schemaFSentenceUniverse_countable (s₀ := s₀)).exists_eq_range
    schemaFSentenceUniverse_nonempty).choose

theorem schemaEnumeration_range :
    Set.range (schemaEnumeration s₀) = schemaFSentenceUniverse s₀ :=
  (((schemaFSentenceUniverse_countable (s₀ := s₀)).exists_eq_range
    schemaFSentenceUniverse_nonempty).choose_spec).symm

variable (ρ : ℕ → FSentence (L'' := localColim s₀) (J := ℕ))
  (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- **The completed theory** (raw set of Marker sentences), the union of the completion stages. -/
def schemaCompletionTheory : Set (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) :=
  {τ | ∃ n, τ ∈ (schemaCompletionStage ρ hM n).1}

/-- **Step 2.** A finite subset of the completed theory lands in a single stage. -/
theorem finite_subset_stage (F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω)) :
    (∀ τ ∈ F, τ ∈ schemaCompletionTheory ρ hM) →
      ∃ N, F ⊆ (schemaCompletionStage ρ hM N).1 := by
  classical
  induction F using Finset.induction with
  | empty => exact fun _ => ⟨0, Finset.empty_subset _⟩
  | @insert a s ha ih =>
    intro hF
    obtain ⟨N₂, hN₂⟩ := hF a (Finset.mem_insert_self a s)
    obtain ⟨N₁, hN₁⟩ := ih (fun τ hτ => hF τ (Finset.mem_insert_of_mem hτ))
    exact ⟨max N₁ N₂, Finset.insert_subset
      (schemaCompletionStage_mono ρ hM (le_max_right N₁ N₂) hN₂)
      (hN₁.trans (schemaCompletionStage_mono ρ hM (le_max_left N₁ N₂)))⟩

/-- **Finite-character consistency**: every finite subset of the completed theory is
`MarkerHenkinConsistent`. -/
theorem schemaCompletionTheory_finite_consistent
    (F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω))
    (hF : ∀ τ ∈ F, τ ∈ schemaCompletionTheory ρ hM) : MarkerHenkinConsistent M F :=
  (schemaCompletionStage_consistent ρ hM (finite_subset_stage ρ hM F hF).choose).mono
    (finite_subset_stage ρ hM F hF).choose_spec

/-- **Step 3 — completeness on the universe**: every schema-universe sentence is decided by the
completed theory (using `range ρ = universe`). -/
theorem schemaCompletionTheory_complete
    (hρrange : Set.range ρ = schemaFSentenceUniverse s₀)
    (τ : FSentence (L'' := localColim s₀) (J := ℕ)) (hτ : τ ∈ schemaFSentenceUniverse s₀) :
    τ.1 ∈ schemaCompletionTheory ρ hM ∨ τ.1.not ∈ schemaCompletionTheory ρ hM := by
  rw [← hρrange] at hτ
  obtain ⟨n, hn⟩ := hτ
  rcases schemaCompletionStage_decides ρ hM n with h | h
  · exact Or.inl ⟨n + 1, hn ▸ h⟩
  · exact Or.inr ⟨n + 1, hn ▸ h⟩

/-- **Step 4/5 — the restricted `iSup`-witness closure.** For a `ΓlocalColim` disjunction
`⟨m, iSup φs⟩` and any tuple `t`, if the lifted `templateSentence (iSup φs) t` is in the completed
theory (over the canonical enumeration), then some component's lifted `templateSentence (φs k) t`
is too. This is exactly the clause `TailTemplateOmegaWitnessed`/R1 consumes — no full `ΓEMlocal`
component closure, no deForm case. The lifted `templateSentence` distributes over `iSup` (`rfl`);
the sentence is a universe member (via `ΓlocalColim ⊆ ΓEMlocal`), so it is some `ρ j`, decided at
stage `j` — positively (a negative decision would put both it and its negation in a common later
stage, contradicting `markerHenkinConsistent_not_mem_and_not_mem`); `schemaCompletionStage_witness`
then supplies the component. -/
theorem schemaCompletionTheory_iSup_witness_localColim
    {m : ℕ} {φs : ℕ → (localColim s₀).BoundedFormulaω Empty m}
    (hmem : (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n)
      ∈ ΓlocalColim s₀)
    (t : Fin m ↪o ℕ)
    (hT : (Lomega1omegaTemplate.templateSentence (BoundedFormulaω.iSup φs) t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)
      ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ k, (Lomega1omegaTemplate.templateSentence (φs k) t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)
      ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  have hdist : (Lomega1omegaTemplate.templateSentence (BoundedFormulaω.iSup φs) t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)
      = BoundedFormulaω.iSup (fun k => (Lomega1omegaTemplate.templateSentence (φs k) t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)) := rfl
  have hmemEM : (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n)
      ∈ ΓEMlocal s₀ := Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hmem))
  have huniv : (⟨(Lomega1omegaTemplate.templateSentence (BoundedFormulaω.iSup φs) t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ),
      hasFiniteConstSupport_mapLanguage_templateSentence (BoundedFormulaω.iSup φs) t⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ :=
    Set.mem_biUnion hmemEM ⟨t, rfl⟩
  rw [← schemaEnumeration_range] at huniv
  obtain ⟨j, hj⟩ := huniv
  have hj1 : (schemaEnumeration s₀ j).1 =
      (Lomega1omegaTemplate.templateSentence (BoundedFormulaω.iSup φs) t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ) := congrArg Subtype.val hj
  have hjT : (schemaEnumeration s₀ j).1 ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    rw [hj1]; exact hT
  rcases schemaCompletionStage_decides (schemaEnumeration s₀) hM j with hpos | hneg
  · have hiSup : (schemaEnumeration s₀ j).1 =
        BoundedFormulaω.iSup (fun k => (Lomega1omegaTemplate.templateSentence (φs k) t).mapLanguage
          (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)) := hj1.trans hdist
    obtain ⟨k, hk⟩ := schemaCompletionStage_witness (schemaEnumeration s₀) hM j hiSup hpos
    exact ⟨k, ⟨j + 1, hk⟩⟩
  · exfalso
    obtain ⟨jn, hjn⟩ := hjT
    exact markerHenkinConsistent_not_mem_and_not_mem
      (schemaCompletionStage_consistent (schemaEnumeration s₀) hM (max jn (j + 1)))
      (schemaEnumeration s₀ j).1
      ⟨schemaCompletionStage_mono (schemaEnumeration s₀) hM (le_max_left jn (j + 1)) hjn,
        schemaCompletionStage_mono (schemaEnumeration s₀) hM (le_max_right jn (j + 1)) hneg⟩

/-- **The `iSup`-witness closure on the universe.** For a universe member `τ` of `iSup` shape
present in the completed theory (over the canonical enumeration), some component is present too —
read off the stage that decided `τ`, as in `schemaCompletionTheory_iSup_witness_localColim` but
generic in the universe member (the canonical-deForm closure in 5b-2 instantiates it). -/
theorem schemaCompletionTheory_iSup_witness_of_universe
    (τ : FSentence (L'' := localColim s₀) (J := ℕ)) (hτ : τ ∈ schemaFSentenceUniverse s₀)
    {φs : ℕ → ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω}
    (hiSup : τ.1 = BoundedFormulaω.iSup φs)
    (hpos : τ.1 ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ k, φs k ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  rw [← schemaEnumeration_range] at hτ
  obtain ⟨j, hj⟩ := hτ
  have hj1 : (schemaEnumeration s₀ j).1 = τ.1 := congrArg Subtype.val hj
  rcases schemaCompletionStage_decides (schemaEnumeration s₀) hM j with hposstage | hnegstage
  · obtain ⟨k, hk⟩ := schemaCompletionStage_witness (schemaEnumeration s₀) hM j
      (hj1.trans hiSup) hposstage
    exact ⟨k, ⟨j + 1, hk⟩⟩
  · exfalso
    obtain ⟨jn, hjn⟩ := hpos
    exact markerHenkinConsistent_not_mem_and_not_mem
      (schemaCompletionStage_consistent (schemaEnumeration s₀) hM (max jn (j + 1)))
      (schemaEnumeration s₀ j).1
      ⟨schemaCompletionStage_mono (schemaEnumeration s₀) hM (le_max_left jn (j + 1))
          (by rw [hj1]; exact hjn),
        schemaCompletionStage_mono (schemaEnumeration s₀) hM (le_max_right jn (j + 1)) hnegstage⟩

/-- **The negative `iInf`-witness closure on the universe.** For a universe member `τ` of `iInf`
shape whose negation is in the completed theory (over the canonical enumeration), some refuted
component `(φs k).not` is in the theory too. This is the direction the restricted truth lemma's
`iInf` case needs (`(∀ k, ⊨ φs k) → ⊨ iInf φs`, contrapositively), and it is NOT derivable from
finite consistency after the theory is formed — the failing component would drift with the
certificate body. It is read off the stage that decided `τ`, exactly as in
`schemaCompletionTheory_iSup_witness_localColim`. -/
theorem schemaCompletionTheory_neg_iInf_witness_of_universe
    (τ : FSentence (L'' := localColim s₀) (J := ℕ)) (hτ : τ ∈ schemaFSentenceUniverse s₀)
    {φs : ℕ → ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω}
    (hiInf : τ.1 = BoundedFormulaω.iInf φs)
    (hneg : τ.1.not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ k, (φs k).not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  rw [← schemaEnumeration_range] at hτ
  obtain ⟨j, hj⟩ := hτ
  have hj1 : (schemaEnumeration s₀ j).1 = τ.1 := congrArg Subtype.val hj
  rcases schemaCompletionStage_decides (schemaEnumeration s₀) hM j with hpos | hnegstage
  · exfalso
    obtain ⟨jn, hjn⟩ := hneg
    exact markerHenkinConsistent_not_mem_and_not_mem
      (schemaCompletionStage_consistent (schemaEnumeration s₀) hM (max (j + 1) jn))
      (schemaEnumeration s₀ j).1
      ⟨schemaCompletionStage_mono (schemaEnumeration s₀) hM (le_max_left (j + 1) jn) hpos,
        schemaCompletionStage_mono (schemaEnumeration s₀) hM (le_max_right (j + 1) jn)
          (by rw [hj1]; exact hjn)⟩
  · obtain ⟨k, hk⟩ := schemaCompletionStage_neg_iInf_witness (schemaEnumeration s₀) hM j
      (hj1.trans hiInf) hnegstage
    exact ⟨k, ⟨j + 1, hk⟩⟩

/-- **Checkpoint 3c bundle.** The three properties of the completed schema theory over the
canonical enumeration `schemaEnumeration s₀`: finite-character consistency, completeness on the
schema universe, and the `ΓlocalColim`-restricted `iSup`-witness closure. Bundling keeps
checkpoints 4/5 from re-threading `ρ`, the range fact, and monotonicity. -/
structure SchemaCompletionTheorySpec (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    Prop where
  /-- Every finite subset of the completed theory is `MarkerHenkinConsistent`. -/
  finite_consistent : ∀ F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω),
    (∀ τ ∈ F, τ ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) → MarkerHenkinConsistent M F
  /-- Every schema-universe sentence is decided by the completed theory. -/
  complete_on_universe : ∀ τ : FSentence (L'' := localColim s₀) (J := ℕ),
    τ ∈ schemaFSentenceUniverse s₀ →
      τ.1 ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ∨
        τ.1.not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM
  /-- A `ΓlocalColim` disjunction present in the theory has a component present. -/
  iSup_witness_localColim : ∀ {m : ℕ} {φs : ℕ → (localColim s₀).BoundedFormulaω Empty m},
    (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ →
      ∀ t : Fin m ↪o ℕ,
        (Lomega1omegaTemplate.templateSentence (BoundedFormulaω.iSup φs) t).mapLanguage
            (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ) ∈
          schemaCompletionTheory (schemaEnumeration s₀) hM →
        ∃ k, (Lomega1omegaTemplate.templateSentence (φs k) t).mapLanguage
            (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ) ∈
          schemaCompletionTheory (schemaEnumeration s₀) hM

/-- **Checkpoint 3c complete**: the completed schema theory over `schemaEnumeration s₀` satisfies
the bundle — the witnessed schema object the extraction (checkpoint 5) consumes. -/
theorem schemaCompletionTheorySpec (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    SchemaCompletionTheorySpec (s₀ := s₀) (M := M) hM where
  finite_consistent := schemaCompletionTheory_finite_consistent (schemaEnumeration s₀) hM
  complete_on_universe :=
    schemaCompletionTheory_complete (schemaEnumeration s₀) hM schemaEnumeration_range
  iSup_witness_localColim := fun hmem t hT =>
    schemaCompletionTheory_iSup_witness_localColim hM hmem t hT

end Union

/-! ## Checkpoint 5b-1, part 1: the finite interpolation engine

Tuple uniformity (part 2) needs, for two length-`m` increasing tuples `t t'` into `ℕ` and ONE
certificate body, two admissible skeleton interpretations `σ₁ σ₂` whose tuple images agree:
`σ₁ ∘ t = σ₂ ∘ t'`. The engine is a global equalizer on `ℕ`: strictly monotone `q q' : ℕ → ℕ`
sending the anchors `p i`/`p' i` to the common value `p i + p' i` — `q` shifts by the largest
passed `p'`-anchor (a `Finset.sup` over a filter), so no piecewise case analysis is needed.
`exists_admissible_pair` threads the equalized values through a `Fin K`-suborder of the
(infinite) certificate domain. Crucially, `MarkerHenkinBody` constrains `σ` only ON the support
`S`, so the tuples need not lie in `S`: they enter only the auxiliary bounding set that picks
`K` — the Marker support itself is never enlarged. -/

section Interpolation

/-- The equalizer shift: the largest `p'`-anchor whose `p`-anchor has been passed. -/
private def equalizerShift {m : ℕ} (p' : Fin m → ℕ) (p : Fin m → ℕ) (x : ℕ) : ℕ :=
  (Finset.univ.filter fun i => p i ≤ x).sup p'

private theorem equalizerShift_mono {m : ℕ} (p' : Fin m → ℕ) (p : Fin m → ℕ) :
    Monotone (equalizerShift p' p) := by
  intro x y hxy
  apply Finset.sup_mono
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans hxy⟩

private theorem equalizerShift_anchor {m : ℕ} {p p' : Fin m → ℕ}
    (hp : StrictMono p) (hp' : StrictMono p') (i : Fin m) :
    equalizerShift p' p (p i) = p' i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    rw [Finset.mem_filter] at hj
    exact hp'.monotone ((hp.le_iff_le).mp hj.2)
  · apply Finset.le_sup
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, le_rfl⟩

/-- **The global equalizer.** Two strictly monotone tuples `p p' : Fin m → ℕ` are equalized by
strictly monotone `q q' : ℕ → ℕ`: `q (p i) = q' (p' i)` (both anchors land at `p i + p' i`). -/
theorem exists_strictMono_equalizer {m : ℕ} (p p' : Fin m → ℕ)
    (hp : StrictMono p) (hp' : StrictMono p') :
    ∃ q q' : ℕ → ℕ, StrictMono q ∧ StrictMono q' ∧
      ∀ i, q (p i) = q' (p' i) := by
  let q : ℕ → ℕ := fun x => x + equalizerShift p' p x
  let q' : ℕ → ℕ := fun x => equalizerShift p p' x + x
  have hq : StrictMono q := by
    intro x y hxy
    exact Nat.add_lt_add_of_lt_of_le hxy (equalizerShift_mono p' p hxy.le)
  have hq' : StrictMono q' := by
    intro x y hxy
    exact Nat.add_lt_add_of_le_of_lt (equalizerShift_mono p p' hxy.le) hxy
  refine ⟨q, q', hq, hq', fun i => ?_⟩
  rw [show q (p i) = p i + equalizerShift p' p (p i) from rfl,
    show q' (p' i) = equalizerShift p p' (p' i) + p' i from rfl,
    equalizerShift_anchor hp hp' i, equalizerShift_anchor hp' hp i,
    Nat.add_comm]

/-- **The admissible pair.** For a finite support `S`, a suborder `e : D ↪o M` with infinite
domain, and two increasing tuples `t t' : Fin m ↪o ℕ`, there are skeleton interpretations
`σ₁ σ₂ : ℕ → M` — each strictly monotone on `S` with `S`-values in `range e` (the
`MarkerHenkinBody` admissibility) — whose tuple images agree: `σ₁ ∘ t = σ₂ ∘ t'`. This is what
lets ONE certificate body be applied twice, once per tuple, in tuple uniformity. -/
theorem exists_admissible_pair
    {M D : Type} [LinearOrder M] [LinearOrder D] [Infinite D]
    {m : ℕ} (S : Finset ℕ) (e : D ↪o M)
    (t t' : Fin m ↪o ℕ) (dflt : M) :
    ∃ σ₁ σ₂ : ℕ → M,
      StrictMonoOn σ₁ ↑S ∧ (∀ j ∈ S, σ₁ j ∈ Set.range e) ∧
      StrictMonoOn σ₂ ↑S ∧ (∀ j ∈ S, σ₂ j ∈ Set.range e) ∧
      ∀ i, σ₁ (t i) = σ₂ (t' i) := by
  classical
  obtain ⟨q, q', hq, hq', heq⟩ :=
    exists_strictMono_equalizer t t' t.strictMono t'.strictMono
  let A : Finset ℕ := (S ∪ Finset.univ.image t) ∪ Finset.univ.image t'
  let B : ℕ := A.sup id
  let K : ℕ := max (q B) (q' B) + 1
  let dEmb : Fin K ↪o D := Classical.choice (exists_orderEmb_fin K)
  have hbound_q {j : ℕ} (hj : j ∈ A) : q j < K := by
    have hjB : j ≤ B := by
      dsimp only [B]
      exact Finset.le_sup (f := id) hj
    calc
      q j ≤ q B := hq.monotone hjB
      _ ≤ max (q B) (q' B) := le_max_left _ _
      _ < max (q B) (q' B) + 1 := Nat.lt_succ_self _
  have hbound_q' {j : ℕ} (hj : j ∈ A) : q' j < K := by
    have hjB : j ≤ B := by
      dsimp only [B]
      exact Finset.le_sup (f := id) hj
    calc
      q' j ≤ q' B := hq'.monotone hjB
      _ ≤ max (q B) (q' B) := le_max_right _ _
      _ < max (q B) (q' B) + 1 := Nat.lt_succ_self _
  let σ₁ : ℕ → M := fun j =>
    if hj : q j < K then e (dEmb ⟨q j, hj⟩) else dflt
  let σ₂ : ℕ → M := fun j =>
    if hj : q' j < K then e (dEmb ⟨q' j, hj⟩) else dflt
  have hSA {j : ℕ} (hj : j ∈ S) : j ∈ A := by
    simp only [A, Finset.mem_union]
    exact Or.inl (Or.inl hj)
  have htA (i : Fin m) : t i ∈ A := by
    simp only [A, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image_of_mem t (Finset.mem_univ i)))
  have htA' (i : Fin m) : t' i ∈ A := by
    simp only [A, Finset.mem_union]
    exact Or.inr (Finset.mem_image_of_mem t' (Finset.mem_univ i))
  refine ⟨σ₁, σ₂, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · intro a ha b hb hab
    rw [show σ₁ a = if h : q a < K then e (dEmb ⟨q a, h⟩) else dflt from rfl,
      show σ₁ b = if h : q b < K then e (dEmb ⟨q b, h⟩) else dflt from rfl,
      dite_eq_left (hbound_q (hSA (Finset.mem_coe.mp ha))),
      dite_eq_left (hbound_q (hSA (Finset.mem_coe.mp hb)))]
    exact e.strictMono (dEmb.strictMono (hq hab))
  · intro j hj
    rw [show σ₁ j = if h : q j < K then e (dEmb ⟨q j, h⟩) else dflt from rfl,
      dite_eq_left (hbound_q (hSA hj))]
    exact ⟨dEmb ⟨q j, hbound_q (hSA hj)⟩, rfl⟩
  · intro a ha b hb hab
    rw [show σ₂ a = if h : q' a < K then e (dEmb ⟨q' a, h⟩) else dflt from rfl,
      show σ₂ b = if h : q' b < K then e (dEmb ⟨q' b, h⟩) else dflt from rfl,
      dite_eq_left (hbound_q' (hSA (Finset.mem_coe.mp ha))),
      dite_eq_left (hbound_q' (hSA (Finset.mem_coe.mp hb)))]
    exact e.strictMono (dEmb.strictMono (hq' hab))
  · intro j hj
    rw [show σ₂ j = if h : q' j < K then e (dEmb ⟨q' j, h⟩) else dflt from rfl,
      dite_eq_left (hbound_q' (hSA hj))]
    exact ⟨dEmb ⟨q' j, hbound_q' (hSA hj)⟩, rfl⟩
  · rw [show σ₁ (t i) =
        if h : q (t i) < K then e (dEmb ⟨q (t i), h⟩) else dflt from rfl,
      show σ₂ (t' i) =
        if h : q' (t' i) < K then e (dEmb ⟨q' (t' i), h⟩) else dflt from rfl,
      dite_eq_left (hbound_q (htA i)), dite_eq_left (hbound_q' (htA' i))]
    apply congrArg e
    apply congrArg dEmb
    apply Fin.ext
    exact heq i

end Interpolation

/-! ## Checkpoint 5b-1, part 2: tuple uniformity

The completed schema theory decides a template sentence's sign **by its `ΓEMlocal` body alone**,
uniformly across the instantiating tuples: `schemaLift ψ t ∈ Tσ ↔ schemaLift ψ t' ∈ Tσ`. This is
the internal form of Marker §5.2's indiscernibility-equivalence axioms, and it is what makes the
term model's canonical sequence genuinely indiscernible for the completed schema (5b-3).

The proof is the honest two-interpretation argument: if `ψ t` is in and `ψ t'` is out, then (by
completeness on the universe) `{schemaLift ψ u, (schemaLift ψ v).not}` is a finite subset of the
theory, hence `MarkerHenkinConsistent`; its ONE certificate body is universal over admissible
skeleton interpretations, so it applies separately to the `exists_admissible_pair` pair
`σ₁, σ₂` — the first realizes `ψ` on `σ₁ ∘ t`, the second refutes `ψ` on `σ₂ ∘ t'`, and those
tuples are EQUAL. No single interpretation is asked to equalize both tuples (strictness would
forbid it); no Henkin witness dependence arises on this single-expansion path. -/

section TupleUniform

/-- **The schema lift**: a template sentence over `(localColim s₀)[[ℕ]]`, lifted along the Henkin
inclusion into the Marker double expansion — the form in which the completed theory holds the
schema universe. Public API: 5b-3's restricted truth lemma states its atomic clauses in exactly
these terms. -/
abbrev schemaLift {s₀ : LocalStage} {m : ℕ}
    (ψ : (localColim s₀).BoundedFormulaω Empty m) (t : Fin m ↪o ℕ) :
    ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω :=
  (Lomega1omegaTemplate.templateSentence ψ t).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)

/-- Every schema lift of a `ΓEMlocal` member is a universe member (with its canonical
finite-support proof). -/
theorem schemaLift_mem_universe {s₀ : LocalStage} {m : ℕ}
    {ψ : (localColim s₀).BoundedFormulaω Empty m}
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t : Fin m ↪o ℕ) :
    (⟨schemaLift ψ t, hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ :=
  Set.mem_biUnion hψ ⟨t, rfl⟩

variable {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- **Checkpoint 5b-1 — tuple uniformity.** The completed schema theory gives every `ΓEMlocal`
body a tuple-independent sign: for same-arity increasing tuples `t t'`, the lifted
`templateSentence ψ t` is in the theory iff the lifted `templateSentence ψ t'` is. -/
theorem schemaCompletionTheory_tuple_uniform
    {m : ℕ} {ψ : (localColim s₀).BoundedFormulaω Empty m}
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t t' : Fin m ↪o ℕ) :
    schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift ψ t' ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  classical
  have transfer : ∀ (u v : Fin m ↪o ℕ),
      schemaLift ψ u ∈ schemaCompletionTheory (schemaEnumeration s₀) hM →
        schemaLift ψ v ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    intro u v hu
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaLift_mem_universe hψ v) with hv | hnv
    · exact hv
    · exfalso
      let F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) :=
        {schemaLift ψ u, (schemaLift ψ v).not}
      have hF : ∀ τ ∈ F,
          τ ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
        intro τ hτ
        change τ ∈ {schemaLift ψ u, (schemaLift ψ v).not} at hτ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
        rcases hτ with rfl | rfl
        · exact hu
        · exact hnv
      obtain ⟨S, H, hS, hH, hcof⟩ :=
        (schemaCompletionTheorySpec hM).finite_consistent F hF
      obtain ⟨α, hα0, hα1, hbody⟩ := hcof 0 (Ordinal.omega_pos 1)
      obtain ⟨e, hsat⟩ := hbody
      let D := (Order.succ (Cardinal.beth α)).ord.ToType
      have : Infinite D := by
        rw [show D = (Order.succ (Cardinal.beth α)).ord.ToType from rfl,
          Cardinal.infinite_iff, Cardinal.mk_ord_toType]
        exact (Cardinal.aleph0_le_beth α).trans (Order.le_succ _)
      let dflt : M := e (Classical.arbitrary D)
      obtain ⟨σ₁, σ₂, hσ₁mono, hσ₁range, hσ₂mono, hσ₂range, heq⟩ :=
        exists_admissible_pair S e u v dflt
      obtain ⟨w₁, hw₁⟩ := hsat σ₁ hσ₁mono hσ₁range
      obtain ⟨w₂, hw₂⟩ := hsat σ₂ hσ₂mono hσ₂range
      have hpos := hw₁ (schemaLift ψ u) (by
        rw [Finset.mem_coe]
        exact Finset.mem_insert_self _ _)
      have hneg := hw₂ (schemaLift ψ v).not (by
        rw [Finset.mem_coe]
        change (schemaLift ψ v).not ∈ {schemaLift ψ u, (schemaLift ψ v).not}
        simp)
      rw [schemaLift, realizeWith_templateSentence] at hpos
      rw [realizeWith_not, schemaLift, realizeWith_templateSentence] at hneg
      apply hneg
      rw [show (fun i => σ₂ (v i)) = fun i => σ₁ (u i) from
        funext fun i => (heq i).symm]
      exact hpos
  exact ⟨transfer t t', transfer t' t⟩

end TupleUniform

/-! ## Checkpoint 5b-2: connective witnesses for canonical deForms

`TailTemplateOmegaWitnessed` — the 5b-3 target — is stated on `canonDeForm (localColim s₀) φ g`,
not on the raw `ΓlocalColim` connectives, so the completed theory's witness closures must be
exposed in exactly those terms. Both directions are corollaries of the universe-level closures:
`canonDeForm` and `schemaLift` each distribute over `iSup`/`iInf` definitionally, and
`canonDeForm_mem_ΓEMlocal` puts the deForm in the universe. The negative direction is the whole
point of the completion repair: the fixed refuted conjunct was pinned at decision time and is
simply read off here. -/

section CanonDeFormWitness

variable {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- **Positive `iSup` witness, canonical-deForm form.** If the lifted template sentence of a
`ΓlocalColim` disjunction's deForm is in the completed theory, so is some component's. -/
theorem schemaCompletionTheory_iSup_witness_canonDeForm
    {m : ℕ} {φs : ℕ → (localColim s₀).BoundedFormulaω Empty m}
    (hmem : (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n)
      ∈ ΓlocalColim s₀)
    {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)) (t : Fin p ↪o ℕ)
    (hT : schemaLift (canonDeForm (localColim s₀) (BoundedFormulaω.iSup φs) g) t
      ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ k, schemaLift (canonDeForm (localColim s₀) (φs k) g) t
      ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  schemaCompletionTheory_iSup_witness_of_universe hM
    ⟨schemaLift (canonDeForm (localColim s₀) (BoundedFormulaω.iSup φs) g) t,
      hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩
    (schemaLift_mem_universe (canonDeForm_mem_ΓEMlocal hmem g) t)
    (φs := fun k => schemaLift (canonDeForm (localColim s₀) (φs k) g) t) rfl hT

/-- **Negative `iInf` witness, canonical-deForm form.** If the negation of the lifted template
sentence of a `ΓlocalColim` conjunction's deForm is in the completed theory, some component's
negation is too — the fixed refuted conjunct the restricted truth lemma's `iInf` case consumes. -/
theorem schemaCompletionTheory_neg_iInf_witness_canonDeForm
    {m : ℕ} {φs : ℕ → (localColim s₀).BoundedFormulaω Empty m}
    (hmem : (⟨m, BoundedFormulaω.iInf φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n)
      ∈ ΓlocalColim s₀)
    {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)) (t : Fin p ↪o ℕ)
    (hneg : (schemaLift (canonDeForm (localColim s₀) (BoundedFormulaω.iInf φs) g) t).not
      ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ k, (schemaLift (canonDeForm (localColim s₀) (φs k) g) t).not
      ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  schemaCompletionTheory_neg_iInf_witness_of_universe hM
    ⟨schemaLift (canonDeForm (localColim s₀) (BoundedFormulaω.iInf φs) g) t,
      hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩
    (schemaLift_mem_universe (canonDeForm_mem_ΓEMlocal hmem g) t)
    (φs := fun k => schemaLift (canonDeForm (localColim s₀) (φs k) g) t) rfl hneg

end CanonDeFormWitness

end FirstOrder.Language
