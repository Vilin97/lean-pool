/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalSkolem
/-!
# The countable local Skolem tower `Llocal` / `Γlocal`

`localSkolem L Γ` (in `LocalSkolem.lean`) adjoins a Skolem function symbol only for the
formulas of a **countable** family `Γ`, and so stays countable. But one layer is not closed under
its own witness formulas, so — exactly as `skolemStage`/`skolemColim` do for the *uncountable*
full Skolemization — we iterate. Here the family `Γ` grows *in lock-step* with the language, so
the language and the family are **mutually recursive**:

* `L₀ = L`, `Γ₀` = the seed family;
* `L_{k+1} = L_k.sum (localSkolem L_k (skolemNeed Γ_k))` — adjoin Skolem symbols for the
  **Skolem-need family** `skolemNeed Γ_k = Γ_k ∪ {¬ψ | ∀ψ ∈ Γ_k}`: the EM truth lemma's `all` case
  consumes the witness symbol of the *negated body* `¬ψ` (cf. `skWitnessStep` in
  `SkolemClosure.lean` and `skWitnessTerm … ψ₀.not` in `EMTermModel.lean`), so Skolemizing `Γ_k`
  alone would miss exactly the symbol the rebased truth lemma needs;
* `Γ_{k+1}` = the subformula/component closure of a seed built from `skolemNeed Γ_k` (lifted along
  the language inclusion), the Skolem-witness bodies of the new symbols, and a reserved
  deForm-closure slot.

The mutual recursion is packaged as one `ℕ`-indexed sequence of `LocalStage` bundles
(language plus family and countability certificates), sidestepping dependent-recursion sprawl.
The **deliverable of
this chunk** is that every stage is countable — both the language's symbol types and the family
`Γ_k` — which is what keeps the eventual local colimit `L_Γ` countable (the fatal size problem that
`localSkolem` was introduced to fix). The local colimit, its cocone inclusions, and the transported
countability live in `LocalColimit.lean`; here we stop at the tower and its stagewise countability.
-/

universe u v w

namespace FirstOrder.Language

/-! ### Countability of `Language.sum` symbol types

A sum language's arity-graded symbol type is the fibrewise disjoint sum, so its total `Σ`-type is
countable as soon as both summands' `Σ`-types are. These feed the successor-language countability
certificate in `LocalStage.succ`. -/

/-- The full function-symbol type of `L.sum L'` is countable when both summands' are. -/
private theorem sum_sigma_functions_countable {L L' : Language.{0, 0}}
    (h : Countable (Σ n, L.Functions n)) (h' : Countable (Σ n, L'.Functions n)) :
    Countable (Σ n, (L.sum L').Functions n) := by
  have := h; have := h'
  exact
    (Equiv.sigmaSumDistrib (fun n => L.Functions n) (fun n => L'.Functions n)).injective.countable

/-- The full relation-symbol type of `L.sum L'` is countable when both summands' are. -/
private theorem sum_sigma_relations_countable {L L' : Language.{0, 0}}
    (h : Countable (Σ n, L.Relations n)) (h' : Countable (Σ n, L'.Relations n)) :
    Countable (Σ n, (L.sum L').Relations n) := by
  have := h; have := h'
  exact
    (Equiv.sigmaSumDistrib (fun n => L.Relations n) (fun n => L'.Relations n)).injective.countable

variable {L : Language.{0, 0}}

/-! ### The local Skolem witness term and formula

For a symbol of `localSkolem L Γ` — that is, a formula `φ ∈ Γ` of arity `n+1` — the witness body of
`∃ xₙ, φ` is `φ[skolemTerm]`, built with the template pattern `openBounds → subst → relabel` exactly
as `skolemWitnessFormula` does in `SkolemClosure.lean`, but using the *local* Skolem symbol (which
exists precisely because `φ ∈ Γ`). This is the arity-`n` formula, over `L.sum (localSkolem L Γ)`,
added to the successor family. -/

/-- The **local Skolem witness term** for the symbol `sym` (a formula `φ ∈ Γ` of arity `n+1`): the
function symbol `sym` — in the `localSkolem` summand — applied to the argument terms `ts`, as a term
of `L.sum (localSkolem L Γ)`. Local analogue of `skolemTerm`. -/
private def localSkolemTerm {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} {γ : Type*} {n : ℕ}
    (sym : (localSkolem L Γ).Functions n)
    (ts : Fin n → (L.sum (localSkolem L Γ)).Term γ) : (L.sum (localSkolem L Γ)).Term γ :=
  Term.func (Sum.inr sym : (L.sum (localSkolem L Γ)).Functions n) ts

/-- The **local Skolem witness formula** for the symbol `sym` (a formula `φ ∈ Γ` of arity `n+1`):
substitute the local Skolem term for the witnessed last variable of `φ`, yielding the arity-`n`
formula `φ[skolemTerm]` over `L.sum (localSkolem L Γ)`. Local analogue of `skolemWitnessFormula`. -/
def localSkolemWitnessFormula {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} {n : ℕ}
    (sym : (localSkolem L Γ).Functions n) : (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n :=
  ((sym.1.openBounds.mapLanguage (LHom.sumInl : L →ᴸ L.sum (localSkolem L Γ))).subst
    (Fin.snoc (fun i => Term.var i) (localSkolemTerm sym (fun i => Term.var i)))).relabel Sum.inr

/-! ### The Skolem-need family: `Γ` plus the negated bodies of its universals

The EM truth lemma's `all` case for `∀ψ` uses the Skolem witness of the **negation** of the body:
`skWitnessTerm … ψ.not` (mirroring `skWitnessStep` in the full `Γ*`, which adds the witness body of
`¬ψ` for every `.all ψ`). So the successor language must carry a local Skolem symbol for `¬ψ`, not
just for the members of `Γ` themselves. `skolemNeed Γ` is the countable enlargement that provisions
exactly these symbols. -/

/-- The negated body contributed by a single family member: a universal `∀ψ` (arity `n`)
contributes `¬ψ` (arity `n+1`) — the formula whose local Skolem symbol the EM `all`-case consumes;
every other form contributes nothing. -/
private def allNegBody : (Σ n, L.BoundedFormulaω Empty n) → Set (Σ n, L.BoundedFormulaω Empty n)
  | ⟨_, .all ψ⟩ => {⟨_, ψ.not⟩}
  | _ => ∅

/-- `allNegBody` is pointwise countable (a singleton on `∀`, empty otherwise). -/
private theorem allNegBody_countable (p : Σ n, L.BoundedFormulaω Empty n) :
    (allNegBody p).Countable := by
  obtain ⟨n, φ⟩ := p
  cases φ <;> first | exact Set.countable_singleton _ | exact Set.countable_empty

/-- The **Skolem-need family**: `Γ` together with the negated bodies of its universal members.
This — not `Γ` itself — is the family the successor stage Skolemizes. -/
def skolemNeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, L.BoundedFormulaω Empty n) :=
  Γ ∪ ⋃ p ∈ Γ, allNegBody p

/-- The Skolem-need family is countable when `Γ` is. -/
private theorem skolemNeed_countable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (skolemNeed Γ).Countable :=
  hΓ.union (hΓ.biUnion fun p _ => allNegBody_countable p)

/-- `Γ` is contained in its Skolem-need family. -/
private theorem subset_skolemNeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) : Γ ⊆ skolemNeed Γ :=
  Set.subset_union_left

/-- **The guarantee the EM `all`-case needs**: if `∀ψ ∈ Γ` then `¬ψ ∈ skolemNeed Γ`, so the local
Skolem language over `skolemNeed Γ` carries a witness symbol for `∃ xₙ, ¬ψ`. -/
private theorem not_mem_skolemNeed_of_all_mem {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} {n : ℕ}
    {ψ : L.BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ Γ) :
    (⟨n + 1, ψ.not⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ skolemNeed Γ :=
  Or.inr (Set.mem_biUnion h rfl)

/-- The local Skolem **witness symbol** for (the negated body of) a universal family member — the
arity-`n` function symbol of `localSkolem L (skolemNeed Γ)` witnessing `∃ xₙ, ¬ψ`. -/
def skolemNeedSymbol {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} {n : ℕ}
    {ψ : L.BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ Γ) :
    (localSkolem L (skolemNeed Γ)).Functions n :=
  ⟨ψ.not, not_mem_skolemNeed_of_all_mem h⟩

/-! ### Seed of the successor family

The seed of `Γ_{k+1}` (before the subformula/component closure) has three parts. Each is countable
when `Γ` is, so the whole seed is. -/

/-- The **lift** of `Γ` into the successor language `L.sum (localSkolem L Γ)` along the left
injection `LHom.sumInl`. Arity is preserved. -/
private def liftGamma (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  (fun p : Σ n, L.BoundedFormulaω Empty n =>
    (⟨p.1, p.2.mapLanguage (LHom.sumInl : L →ᴸ L.sum (localSkolem L Γ))⟩ :
      Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n)) '' Γ

/-- The lift of a countable family is countable (image of a countable set). -/
private theorem liftGamma_countable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (liftGamma Γ).Countable := hΓ.image _

/-- The **Skolem-witness seed**: the witness formula of every local Skolem symbol. Indexed by the
symbol type `Σ n, (localSkolem L Γ).Functions n`, which is countable when `Γ` is. -/
private def localSkWitnessSeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  Set.range fun sym : Σ n, (localSkolem L Γ).Functions n =>
    (⟨sym.1, localSkolemWitnessFormula sym.2⟩ :
      Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n)

/-- The Skolem-witness seed is countable: it is the range of a map out of the (countable) local
Skolem symbol type. -/
private theorem localSkWitnessSeed_countable
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (localSkWitnessSeed Γ).Countable := by
  have := localSkolem_sigma_functions_countable Γ hΓ
  exact Set.countable_range _

/-- **Reserved deForm-closure seed** (placeholder). The truth lemma's family must be closed under
the *de-substituted* formulas `deForm S φ ts` of its members; but `deForm` is defined over a
term-model carrier `J` (see `EMTermModel.deForm`), which does not exist at the pure language-tower
level. This named slot is empty until the local colimit and its term model are in place. -/
private def deFormSeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) := ∅

/-- The reserved deForm seed is (trivially) countable. -/
private theorem deFormSeed_countable (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (deFormSeed Γ).Countable := Set.countable_empty

/-- The full **seed** of the successor family: the lift of `Γ`, the Skolem-witness bodies, and the
reserved deForm slot. -/
private def localSeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  liftGamma Γ ∪ localSkWitnessSeed Γ ∪ deFormSeed Γ

/-- The successor seed is countable when `Γ` is. -/
private theorem localSeed_countable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (localSeed Γ).Countable :=
  ((liftGamma_countable hΓ).union (localSkWitnessSeed_countable hΓ)).union (deFormSeed_countable Γ)

/-! ### The successor family `Γ_{k+1}` -/

/-- The **successor family**: the subformula/component closure (`setClosure bfSubformulas`) of the
successor seed. Closing under `bfSubformulas` makes `Γ_{k+1}` closed under immediate subformulas
and countable-connective components — the structural-induction requirement of the truth lemma —
while the Skolem-witness and (reserved) deForm generators sit in the seed. -/
private def localGammaNext (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  setClosure bfSubformulas (localSeed Γ)

/-- The successor family is countable when `Γ` is: `setClosure` of a countable seed under the
pointwise-countable subformula step. -/
private theorem localGammaNext_countable
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (localGammaNext Γ).Countable :=
  setClosure_countable bfSubformulas (localSeed_countable hΓ) bfSubformulas_countable

/-- The seed is contained in the successor family. -/
private theorem localSeed_subset_localGammaNext (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    localSeed Γ ⊆ localGammaNext Γ := subset_setClosure _ _

/-! ### The stage bundle and the tower -/

/-- A single **stage** of the local Skolem tower: a language, a family of its formulas, and
countability certificates for the family and the language's symbol types. Bundling these keeps the
mutual language/family recursion a plain `ℕ`-indexed sequence rather than a dependent recursion. -/
structure LocalStage where
  /-- The stage language. -/
  Lang : Language.{0, 0}
  /-- The stage family of formulas of `Lang`. -/
  Gamma : Set (Σ n, Lang.BoundedFormulaω Empty n)
  /-- The stage family is countable. -/
  gamma_countable : Gamma.Countable
  /-- The stage language has countably many function symbols. -/
  fun_countable : Countable (Σ n, Lang.Functions n)
  /-- The stage language has countably many relation symbols. -/
  rel_countable : Countable (Σ n, Lang.Relations n)

/-- The **successor stage**: Skolemize the current **Skolem-need** family
(`Lang.sum (localSkolem Lang (skolemNeed Gamma))` — `skolemNeed` so the EM `all`-case witness
symbol for `¬ψ` of each `∀ψ ∈ Gamma` exists) and replace the family by its successor closure.
Every countability certificate is carried forward: the family via `localGammaNext_countable`, the
language via `sum_sigma_functions_countable` / `sum_sigma_relations_countable` together with
`localSkolem`'s own countability (fed by `skolemNeed_countable`). -/
def LocalStage.succ (s : LocalStage) : LocalStage where
  Lang := s.Lang.sum (localSkolem s.Lang (skolemNeed s.Gamma))
  Gamma := localGammaNext (skolemNeed s.Gamma)
  gamma_countable := localGammaNext_countable (skolemNeed_countable s.gamma_countable)
  fun_countable :=
    sum_sigma_functions_countable s.fun_countable
      (localSkolem_sigma_functions_countable (skolemNeed s.Gamma)
        (skolemNeed_countable s.gamma_countable))
  rel_countable :=
    sum_sigma_relations_countable s.rel_countable
      (localSkolem_sigma_relations_countable (skolemNeed s.Gamma))

/-- The **local Skolem tower** seeded at `s₀`: stage `0` is the seed and each successor Skolemizes
the current stage. -/
def localStage (s₀ : LocalStage) : ℕ → LocalStage
  | 0 => s₀
  | k + 1 => (localStage s₀ k).succ

/-! ### Projections consumed by the later local-colimit chunk -/

/-- The **stage-`k` local language** `L_k`. -/
def Llocal (s₀ : LocalStage) (k : ℕ) : Language.{0, 0} := (localStage s₀ k).Lang

/-- The **stage-`k` local family** `Γ_k`. -/
def Γlocal (s₀ : LocalStage) (k : ℕ) : Set (Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) :=
  (localStage s₀ k).Gamma

/-- The **stage-`k` → stage-`(k+1)` language inclusion**: the left injection of the Skolemizing sum.
The later colimit's cocone is assembled from these. -/
def LlocalHom (s₀ : LocalStage) (k : ℕ) : Llocal s₀ k →ᴸ Llocal s₀ (k + 1) := LHom.sumInl

/-- Each stage-`k` family is countable. -/
theorem Γlocal_countable (s₀ : LocalStage) (k : ℕ) : (Γlocal s₀ k).Countable :=
  (localStage s₀ k).gamma_countable

/-- Each stage-`k` language has countably many function symbols. -/
theorem Llocal_fun_countable (s₀ : LocalStage) (k : ℕ) :
    Countable (Σ n, (Llocal s₀ k).Functions n) := (localStage s₀ k).fun_countable

/-- Each stage-`k` language has countably many relation symbols. -/
theorem Llocal_rel_countable (s₀ : LocalStage) (k : ℕ) :
    Countable (Σ n, (Llocal s₀ k).Relations n) := (localStage s₀ k).rel_countable

/-! ### Family-membership coherence up the tower -/

/-- **Lift stability**: a stage-`k` family member, lifted along the stage inclusion `LlocalHom`,
lies in the successor family (via `subset_skolemNeed`, the `liftGamma` part of the seed, and
`localSeed_subset_localGammaNext`). -/
theorem liftGamma_mem_Γlocal_succ (s₀ : LocalStage) {k : ℕ}
    {p : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n} (hp : p ∈ Γlocal s₀ k) :
    (⟨p.1, p.2.mapLanguage (LlocalHom s₀ k)⟩ :
      Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) ∈ Γlocal s₀ (k + 1) :=
  localSeed_subset_localGammaNext _
    (Or.inl (Or.inl (Set.mem_image_of_mem _ (subset_skolemNeed _ hp))))

/-- **Successor-stage closure**: every successor family is closed under immediate
subformulas/components (it is a `setClosure bfSubformulas`). -/
theorem bfSubformulas_subset_Γlocal_succ (s₀ : LocalStage) {k : ℕ}
    {p : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n} (hp : p ∈ Γlocal s₀ (k + 1)) :
    bfSubformulas p ⊆ Γlocal s₀ (k + 1) :=
  stepOne_subset_setClosure _ _ hp
/-- The lift of the **negated body** of a universal family member is in the successor family (the
seed lifts the whole `skolemNeed` enlargement, not just `Γ_k`). Feeds the local truth lemma's
`all` case, whose Skolemized body `¬ψ` lives one stage up. -/
theorem liftNegBody_mem_Γlocal_succ (s₀ : LocalStage) {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k) :
    (⟨n + 1, (ψ.not).mapLanguage (LlocalHom s₀ k)⟩ :
      Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) ∈ Γlocal s₀ (k + 1) :=
  localSeed_subset_localGammaNext _
    (Or.inl (Or.inl (Set.mem_image_of_mem _ (not_mem_skolemNeed_of_all_mem h))))
end FirstOrder.Language
