/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMTruth
import LeanPool.InfinitaryLogic.Methods.LocalSkolemUniversal
/-!
# The local EM truth lemma, layer 2: readiness + the staged truth lemma

The truth-lemma endpoints of the `EMContext` re-base, ported from `EMTermModel.lean:1030–1379`
(Steps 4D-7 and 4D-9) onto the countable local stack. Three parts.

**Generic readiness** (`section TruthReadiness`, over any `[Λ.Structure M]`): the `⋁`/`⋀`-
completeness mixin `LocalEMContext.OmegaComplete` with its easy directions
(`eventualDeepTruth_iSup_of_exists`, `eventualDeepTruth_iInf_forall`), the decidedness predicate
`LocalEMContext.Decided`, and the recursive readiness predicate `LocalEMContext.TLReady`. Ported
from `EMTermModel.lean:1041–1102` with the `skolemColim` `letI` plumbing dropped (the structure is
the ambient instance, as throughout `LocalEMContext.lean`).

**Staged readiness over `localColim s₀`** (`section StagedReadiness`, over an *arbitrary*
`[(localColim s₀).Structure M]`): the support-uniform staged readiness
`LocalEMContext.TLReadyStage` (`EMTermModel.lean:1117–1127`), the deForm-closure mixin
`LocalEMContext.DeFormClosedForColim` — rephrased over the colimit-level family `ΓlocalColim`
rather than the staged `Γ*` of `EMContext.DeFormClosedForGammaStar` (`EMTermModel.lean:1308–1319`);
staged members reach it via `toLocalColimFormula_mem_ΓlocalColim` — and the family-readiness
endpoints `TLReady_mapLang_of_Γlocal_succ` / `TLReadyStage_of_Γlocal_succ`
(`EMTermModel.lean:1322–1377`). Unlike the EM stack, where the mixin stays an open obligation, here
it has a concrete two-line discharger `deFormClosedForColim_of_ΓEMlocal_subset` (via
`locDeForm_mem_ΓEMlocal`), a **pure parameterized lemma**: it takes `ΓEMlocal s₀ ⊆ ctx.Γ` as a
hypothesis; the application against `exists_localEMContext` (whose context has `ctx.Γ = ΓEMlocal
s₀`) happens downstream in the Conditional-touching extraction layer, not here.

**The staged truth lemma** (`section StagedTruthLemma`, over a source model `[s₀.Lang.Structure M]`
with `letI := localColimStructure s₀` in the statements, as in `locSkWitness_universal`):
`LocalEMContext.truthLemmaStage`, the port of `EMContext.truthLemmaStage`
(`EMTermModel.lean:1129–1291`), plus the stage-`k` lift corollary `truthLemmaStage_of_mem`. Two
deliberate statement-shape divergences from the EM original:

* **Membership threading.** The local Skolem witness `locSkWitnessTerm` exists only for *family
  members* (it is keyed by a `Γlocal`-membership proof, where the EM `skWitnessTerm` takes an
  arbitrary formula), so the induction carries `hmem : ⟨n, ψ⟩ ∈ Γlocal s₀ (k + 1)` and each case
  derives its subformulas' memberships via `bfSubformulas_subset_Γlocal_succ` before applying the
  IH. In the `all` case the memberships split: `hmem` *itself* (the `.all` member) feeds the
  witness API (`locSkWitnessTerm`, `locSkWitness_universal`), while the **body** membership for
  the IH comes from `bfSubformulas_subset_Γlocal_succ hmem`.
* **Successor-stage placement.** Subformula closure of `Γlocal` holds only at successor stages
  (`bfSubformulas_subset_Γlocal_succ`; the stage-`0` seed is raw), so the readiness and truth-lemma
  endpoints are stated for `ψ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n` with membership in
  `Γlocal s₀ (k + 1)`, mapped via `LlocalInclusion s₀ (k + 1)`. The lift corollary
  `truthLemmaStage_of_mem` restores the stage-agnostic form for original stage-`k` members via
  `liftGamma_mem_Γlocal_succ` + the cocone coherence `LlocalInclusion_comp_LlocalHom`.

The completeness input remains an **assumed** mixin (`hc`), but in the honest restricted form
`OmegaCompleteForColim` (= `OmegaCompleteOn` at `ΓlocalColim s₀`): the induction only ever
consumes `⋁`/`⋀`-completeness at colimit images of family members, whose memberships it threads —
while an arbitrary tail-indiscernible sequence can have drifting witnesses for countable
disjunctions outside the family, so the global `OmegaComplete` (kept, with the adapter
`OmegaComplete.toOmegaCompleteOn`) is strictly stronger than any extraction needs to deliver.
Producing the restricted witness ("`ΓlocalColim`-restricted witness homogeneity") is later work,
as is the final connection to `TailTemplateRealizable`. This is a pure file (imports
`LocalEMTruth`, hence the pure local stack only) — no EM-stack or `Conditional/` reach.
-/

namespace FirstOrder.Language

/-! ## Generic truth-lemma readiness

The `⋁`/`⋀`-completeness mixin, decidedness, and the recursive readiness predicate, generic over
any `[Λ.Structure M]`. Ported from `EMTermModel.lean:1041–1102`. -/

section TruthReadiness

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J] {M : Type} [Λ.Structure M]

/-- **`Γ`-restricted, support-covered `⋁`/`⋀`-completeness**: like `OmegaComplete`, but the
uniform `iSup`-witness and uniform `iInf`-cutoff are demanded only at disjunctions/conjunctions
that are **members of the family** `Γ'`, and only at argument tuples whose skeleton support is
**covered** by the ambient support (`hcov`). This is the honest form of the obligation: the
staged truth-lemma induction only ever consumes completeness at colimit images of family members
(their memberships are threaded through the induction) and always under a support-covering proof
(`hsub`), while an arbitrary tail-indiscernible sequence can have *drifting witnesses* for
countable disjunctions outside the family — so the global `OmegaComplete` is strictly stronger
than what any extraction argument needs to deliver. The covering makes the clauses deForm-
normalizable (`eventualDeepTruth_iff_eventual_locDeForm`), hence reducible to the source-side
`LocalEMOmegaHomogeneous` below. -/
structure LocalEMContext.OmegaCompleteOn (ctx : LocalEMContext Λ J (M := M))
    (Γ' : Set (Σ n, Λ.BoundedFormulaω Empty n)) : Prop where
  /-- Eventual deep truth of a family disjunction `⋁φs ∈ Γ'`, over a covered support, provides a
  single component witness. -/
  iSup_complete : ∀ {m : ℕ} (φs : ℕ → Λ.BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ' →
    ∀ (ts : Fin m → Λ[[J]].Term Empty) (S : Finset J),
    (∀ i, locJSupport Λ J (ts i) ⊆ S) →
    LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (BoundedFormulaω.iSup φs) ts S →
      ∃ i, LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (φs i) ts S
  /-- Eventual deep truth of all components of a family conjunction `⋀φs ∈ Γ'`, over a covered
  support, provides eventual deep truth of the conjunction. -/
  iInf_complete : ∀ {m : ℕ} (φs : ℕ → Λ.BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iInf φs⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ' →
    ∀ (ts : Fin m → Λ[[J]].Term Empty) (S : Finset J),
    (∀ i, locJSupport Λ J (ts i) ⊆ S) →
    (∀ i, LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (φs i) ts S) →
      LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (BoundedFormulaω.iInf φs) ts S

/-- The easy `iSup` direction: a single component's eventual deep truth gives the disjunction's. -/
private theorem LocalEMContext.eventualDeepTruth_iSup_of_exists (ctx : LocalEMContext Λ J (M
  := M)) {m : ℕ}
    (φs : ℕ → Λ.BoundedFormulaω Empty m)
    (ts : Fin m → Λ[[J]].Term Empty) (S : Finset J)
    (h : ∃ i, LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (φs i) ts S) :
    LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (BoundedFormulaω.iSup φs) ts S := by
  obtain ⟨i, hi⟩ := h
  simp only [LocalEMContext.eventualDeepTruth, BoundedFormulaω.realize_iSup] at hi ⊢
  exact hi.mono fun _ hd => ⟨i, hd⟩

/-- The easy `iInf` direction: the conjunction's eventual deep truth gives every component's. -/
private theorem LocalEMContext.eventualDeepTruth_iInf_forall (ctx : LocalEMContext Λ J (M :=
  M)) {m : ℕ}
    (φs : ℕ → Λ.BoundedFormulaω Empty m)
    (ts : Fin m → Λ[[J]].Term Empty) (S : Finset J)
    (h : LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (BoundedFormulaω.iInf φs) ts S)
    (i : ℕ) :
    LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (φs i) ts S := by
  simp only [LocalEMContext.eventualDeepTruth, BoundedFormulaω.realize_iInf] at h ⊢
  exact h.mono fun _ hd => hd i

/-! ### deForm normal forms

Over a covered support, eventual deep truth is eventual truth of the **de-substituted source
formula** on consecutive `ctx.a`-tuples — and de-substitution commutes syntactically with the
countable connectives. Together these turn the support-covered Ω-clauses into pure statements
about the source sequence (`LocalEMOmegaHomogeneous` below). -/

/-- **Decidedness of a formula's eventual deep truth** (the named output of
`eventualDeepTruth_decided`): either it holds eventually, or it fails eventually. Local analogue of
`EMContext.Decided`, with the ambient `[Λ.Structure M]` in place of the `skolemColim` `letI`. -/
private def LocalEMContext.Decided (ctx : LocalEMContext Λ J (M := M)) {m : ℕ}
    (φ : Λ.BoundedFormulaω Empty m)
    (ts : Fin m → Λ[[J]].Term Empty) (S : Finset J) : Prop :=
  (∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => locDeepInterp Λ J ctx.a d S (ts i)) ∨
    (∀ᶠ d in Filter.atTop, ¬ φ.Realize Empty.elim fun i => locDeepInterp Λ J ctx.a d S (ts i))

/-- **Truth-lemma readiness** of a formula on `ts`/`S`: the closure data the truth-lemma induction
consumes — decidedness at every `imp`-antecedent (for `eventualDeepTruth_imp_iff`), recursively down
the connectives. The `all φ` case requires the **body** `φ` to be ready at every one-point extension
`Fin.snoc ts u` (the carrier's `∀x` ranges over all term-classes `mkClass u` via `Quotient.ind`), so
the `all` case recurses on the structural subformula `φ` — no Skolem-witness recursion is needed
here. Discharged from the family deForm-closure via `eventualDeepTruth_decided`. Local analogue of
`EMContext.TLReady`. -/
def LocalEMContext.TLReady (ctx : LocalEMContext Λ J (M := M)) :
    ∀ {m : ℕ}, Λ.BoundedFormulaω Empty m → (Fin m → Λ[[J]].Term Empty) → Finset J → Prop
  | _, .falsum, _, _ => True
  | _, .equal _ _, _, _ => True
  | _, .rel _ _, _, _ => True
  | _, .imp φ ψ, ts, S =>
      LocalEMContext.Decided (Λ := Λ) (J := J) ctx φ ts S ∧
        LocalEMContext.TLReady ctx φ ts S ∧ LocalEMContext.TLReady ctx ψ ts S
  | _, .iSup φs, ts, S => ∀ i, LocalEMContext.TLReady ctx (φs i) ts S
  | _, .iInf φs, ts, S => ∀ i, LocalEMContext.TLReady ctx (φs i) ts S
  | _, .all φ, ts, S =>
      ∀ u : Λ[[J]].Term Empty,
        LocalEMContext.TLReady ctx φ (Fin.snoc ts u) (S ∪ locJSupport Λ J u)

end TruthReadiness

/-! ## Staged readiness over `localColim s₀`

The support-uniform staged readiness, the colimit-level deForm-closure mixin with its `ΓEMlocal`
discharger, and the family-readiness endpoints. Over an *arbitrary*
`[(localColim s₀).Structure M]` — no source-model semantics enters until the truth lemma itself. -/

section StagedReadiness

variable (s₀ : LocalStage) (J : Type) [LinearOrder J] {M : Type} [(localColim s₀).Structure M]

/-- **Staged truth-lemma readiness** (support-*uniform*): the colimit `TLReady` of the staged
formula's image under `LlocalInclusion k` holds at *every* enlarged support `T ⊇ S`. The uniformity
is what the `all` case needs — it reads the body's readiness at `S ∪ locJSupport u` (for the Skolem
witness, whose own support is `⊆ S`). Monotone in `S` by construction; the successor-stage family
discharges it uniformly (`TLReadyStage_of_Γlocal_succ`). Local analogue of
`EMContext.TLReadyStage`. -/
def LocalEMContext.TLReadyStage (ctx : LocalEMContext (localColim s₀) J (M := M)) (k : ℕ) {n : ℕ}
    (ψ : (Llocal s₀ k).BoundedFormulaω Empty n)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) (S : Finset J) : Prop :=
  ∀ T : Finset J, S ⊆ T →
    LocalEMContext.TLReady (Λ := localColim s₀) (J := J) ctx
      (ψ.mapLanguage (LlocalInclusion s₀ k)) ts T

/-- **The colimit-family completeness obligation** — the exact `⋁`/`⋀`-completeness the staged
truth lemma consumes: `OmegaCompleteOn` at the colimit family `ΓlocalColim s₀`. This, not the
global `OmegaComplete`, is the final residual shape the witness-homogeneous extraction has to
deliver ("`ΓlocalColim`-restricted witness homogeneity"). -/
abbrev LocalEMContext.OmegaCompleteForColim
    (ctx : LocalEMContext (localColim s₀) J (M := M)) : Prop :=
  LocalEMContext.OmegaCompleteOn (Λ := localColim s₀) (J := J) ctx (ΓlocalColim s₀)

/-- **Source-side Ω-homogeneity of a sequence** — the deForm normal form of the support-covered
completeness obligation, freed of the term model entirely: no `J`, no supports, no quotient, no
`LocalEMContext`. For each family disjunction/conjunction (member of `ΓlocalColim s₀`) and each
**canonical** de-substitution tuple `g` (through which every `J`/`ts`/`S` instance factors, via
`locDeTermFin`), the uniform witness/cutoff exchange holds for the eventual truth of the
de-substituted components on consecutive `a`-tuples. This is a pure statement about the sequence
`a` in the source model — the shape the remaining combinatorial extraction has to homogenize. -/
structure LocalEMOmegaHomogeneous (s₀ : LocalStage) {M : Type} [(localColim s₀).Structure M]
    (a : ℕ → M) : Prop where
  /-- Uniform `iSup`-witness: if, eventually in depth, *some* de-substituted component of a
  family disjunction holds on the consecutive tuple, then a *single* component eventually
  holds. -/
  iSup_homogeneous : ∀ {m : ℕ} (φs : ℕ → (localColim s₀).BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iSup φs⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ →
    ∀ {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)),
    (∀ᶠ d in Filter.atTop, ∃ i, (canonDeForm (localColim s₀) (φs i) g).Realize
        (Empty.elim : Empty → M) (fun k : Fin p => a (d + (k : ℕ)))) →
    ∃ i, ∀ᶠ d in Filter.atTop, (canonDeForm (localColim s₀) (φs i) g).Realize
        (Empty.elim : Empty → M) (fun k : Fin p => a (d + (k : ℕ)))
  /-- Uniform `iInf`-cutoff: if every de-substituted component of a family conjunction
  eventually holds on the consecutive tuple, then eventually *all* components hold
  simultaneously. -/
  iInf_homogeneous : ∀ {m : ℕ} (φs : ℕ → (localColim s₀).BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iInf φs⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ →
    ∀ {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)),
    (∀ i, ∀ᶠ d in Filter.atTop, (canonDeForm (localColim s₀) (φs i) g).Realize
        (Empty.elim : Empty → M) (fun k : Fin p => a (d + (k : ℕ)))) →
    ∀ᶠ d in Filter.atTop, ∀ i, (canonDeForm (localColim s₀) (φs i) g).Realize
        (Empty.elim : Empty → M) (fun k : Fin p => a (d + (k : ℕ)))

/-- **The reduction theorem**: source-side Ω-homogeneity of the context's sequence delivers the
support-covered colimit-family completeness — the term-model side of the obligation dissolves.
Each Ω-clause converts pointwise through `realize_locDeForm` (with `locDeForm` *definitionally*
the canonical deForm at the `locDeTermFin` tuple, so the homogeneity fields apply at
`g := locDeTermFin ∘ ts`), and `realize_iSup`/`realize_iInf` split the connective on the deep
side. After this, the remaining extraction target is `LocalEMOmegaHomogeneous` alone. -/
theorem LocalEMContext.omegaCompleteForColim_of_omegaHomogeneous
    (ctx : LocalEMContext (localColim s₀) J (M := M))
    (h : LocalEMOmegaHomogeneous s₀ ctx.a) :
    LocalEMContext.OmegaCompleteForColim s₀ J ctx := by
  constructor
  · intro m φs hmem ts S hcov hev
    have hev' : ∀ᶠ d in Filter.atTop, ∃ i,
        (canonDeForm (localColim s₀) (φs i)
            (fun i => locDeTermFin (localColim s₀) J S (ts i) (hcov i))).Realize
          (Empty.elim : Empty → M) (fun k : Fin S.card => ctx.a (d + (k : ℕ))) := by
      rw [LocalEMContext.eventualDeepTruth] at hev
      refine hev.mono fun d hd => ?_
      rw [BoundedFormulaω.realize_iSup] at hd
      obtain ⟨i, hi⟩ := hd
      exact ⟨i, (realize_locDeForm (localColim s₀) J ctx.a d S (φs i) ts hcov).mpr hi⟩
    obtain ⟨i, hi⟩ := h.iSup_homogeneous φs hmem
      (fun i => locDeTermFin (localColim s₀) J S (ts i) (hcov i)) hev'
    refine ⟨i, ?_⟩
    rw [LocalEMContext.eventualDeepTruth]
    exact hi.mono fun d hd =>
      (realize_locDeForm (localColim s₀) J ctx.a d S (φs i) ts hcov).mp hd
  · intro m φs hmem ts S hcov hev
    have hev' : ∀ i, ∀ᶠ d in Filter.atTop,
        (canonDeForm (localColim s₀) (φs i)
            (fun i => locDeTermFin (localColim s₀) J S (ts i) (hcov i))).Realize
          (Empty.elim : Empty → M) (fun k : Fin S.card => ctx.a (d + (k : ℕ))) := by
      intro i
      have hi := hev i
      rw [LocalEMContext.eventualDeepTruth] at hi
      exact hi.mono fun d hd =>
        (realize_locDeForm (localColim s₀) J ctx.a d S (φs i) ts hcov).mpr hd
    have hcut := h.iInf_homogeneous φs hmem
      (fun i => locDeTermFin (localColim s₀) J S (ts i) (hcov i)) hev'
    rw [LocalEMContext.eventualDeepTruth]
    refine hcut.mono fun d hd => ?_
    rw [BoundedFormulaω.realize_iInf]
    exact fun i => (realize_locDeForm (localColim s₀) J ctx.a d S (φs i) ts hcov).mp (hd i)

/-- **deForm-membership closure** (construction-data mixin, the seam between family readiness and
the extracted family): every colimit-family member's de-substituted formula — **support-uniformly**,
i.e. over every argument tuple `ts`, covering support `T`, and covering proof `hcov` — lies in
`ctx.Γ`. Rephrased over the colimit-level `ΓlocalColim` rather than the staged `Γ*` of
`EMContext.DeFormClosedForGammaStar`; staged members reach it via
`toLocalColimFormula_mem_ΓlocalColim`. Discharged by `deFormClosedForColim_of_ΓEMlocal_subset`. -/
structure LocalEMContext.DeFormClosedForColim
    (ctx : LocalEMContext (localColim s₀) J (M := M)) : Prop where
  /-- Each colimit-family member's deForm, over any covering support and arguments, is in `Γ`. -/
  deForm_mem : ∀ {n : ℕ} {φ : (localColim s₀).BoundedFormulaω Empty n},
    (⟨n, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ →
    ∀ (ts : Fin n → (localColim s₀)[[J]].Term Empty) (T : Finset J)
      (hcov : ∀ i, locJSupport (localColim s₀) J (ts i) ⊆ T),
      (⟨T.card, locDeForm (localColim s₀) J T φ ts hcov⟩ :
        Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ctx.Γ

/-- **The deForm-closure mixin, discharged** (pure parameterized form): any context whose family
contains `ΓEMlocal s₀` is deForm-closed for the colimit family, via `locDeForm_mem_ΓEMlocal`. In
contrast to the EM stack, where `DeFormClosedForGammaStar` stays an open obligation, the local
family was *built* with the canonical deForm closure inside. The hypothesis `hΓ` is discharged
downstream against `exists_localEMContext` (whose context has `ctx.Γ = ΓEMlocal s₀`) — in the
extraction layer, not here, keeping this file pure. -/
theorem LocalEMContext.deFormClosedForColim_of_ΓEMlocal_subset
    (ctx : LocalEMContext (localColim s₀) J (M := M)) (hΓ : ΓEMlocal s₀ ⊆ ctx.Γ) :
    LocalEMContext.DeFormClosedForColim (s₀ := s₀) (J := J) ctx :=
  ⟨fun hφ ts T hcov => hΓ (locDeForm_mem_ΓEMlocal J s₀ T hφ ts hcov)⟩

/-- **Readiness (un-quantified support form)**: from the deForm-closure mixin, every
successor-stage family formula `ψ` has `TLReady` at every covering support `T`. The core
induction; `TLReadyStage_of_Γlocal_succ` wraps it over `T ⊇ S`. Stated at stage `k + 1` because
subformula closure holds only at successor stages (`bfSubformulas_subset_Γlocal_succ`); the
membership recursion descends through it, and the `imp`-antecedent decidedness obligations are
discharged by `eventualDeepTruth_decided` fed by the mixin. Local analogue of
`EMContext.TLReady_mapLang_of_GammaStar`. -/
private theorem LocalEMContext.TLReady_mapLang_of_Γlocal_succ
    (ctx : LocalEMContext (localColim s₀) J (M := M)) {k : ℕ}
    (hclosed : LocalEMContext.DeFormClosedForColim (s₀ := s₀) (J := J) ctx) :
    ∀ {n : ℕ} (ψ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n),
      (⟨n, ψ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) ∈ Γlocal s₀ (k + 1) →
      ∀ (ts : Fin n → (localColim s₀)[[J]].Term Empty) (T : Finset J),
        (∀ i, locJSupport (localColim s₀) J (ts i) ⊆ T) →
        LocalEMContext.TLReady (Λ := localColim s₀) (J := J) ctx
          (ψ.mapLanguage (LlocalInclusion s₀ (k + 1))) ts T := by
  intro n ψ
  induction ψ with
  | falsum => intro _ _ _ _; exact trivial
  | equal t₁ t₂ => intro _ _ _ _; exact trivial
  | rel R args => intro _ _ _ _; exact trivial
  | imp φ' ψ' ihφ ihψ =>
    intro hψ ts T hcov
    have hφ'mem : (⟨_, φ'⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hψ (Set.mem_insert _ _)
    have hψ'mem : (⟨_, ψ'⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hψ (Set.mem_insert_of_mem _ rfl)
    exact ⟨LocalEMContext.eventualDeepTruth_decided (Λ := localColim s₀) (J := J) ctx
        (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) φ') ts T hcov
        (hclosed.deForm_mem (toLocalColimFormula_mem_ΓlocalColim s₀ hφ'mem) ts T hcov),
      ihφ hφ'mem ts T hcov, ihψ hψ'mem ts T hcov⟩
  | iSup φs ih =>
    intro hψ ts T hcov i
    exact ih i (bfSubformulas_subset_Γlocal_succ s₀ hψ (Set.mem_range_self i)) ts T hcov
  | iInf φs ih =>
    intro hψ ts T hcov i
    exact ih i (bfSubformulas_subset_Γlocal_succ s₀ hψ (Set.mem_range_self i)) ts T hcov
  | all χ' ih =>
    intro hψ ts T hcov u
    have hχ'mem : (⟨_, χ'⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hψ rfl
    have hcov' : ∀ i, locJSupport (localColim s₀) J
        ((Fin.snoc ts u : Fin _ → (localColim s₀)[[J]].Term Empty) i)
          ⊆ T ∪ locJSupport (localColim s₀) J u := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact Finset.subset_union_right
      · rw [Fin.snoc_castSucc]; exact (hcov j).trans Finset.subset_union_left
    exact ih hχ'mem (Fin.snoc ts u) (T ∪ locJSupport (localColim s₀) J u) hcov'

/-- **Formula-level cocone coherence for the truth lemma's lift**: mapping a stage-`k` formula one
stage up (along `LlocalHom`) and then into the colimit is the direct colimit image. The formula
component of `toLocalColimFormula_step`, in the un-packaged form the stage-`k` lift corollary
rewrites with. -/
theorem mapLanguage_LlocalInclusion_lift {k n : ℕ} (ψ : (Llocal s₀ k).BoundedFormulaω Empty n) :
    (ψ.mapLanguage (LlocalHom s₀ k)).mapLanguage (LlocalInclusion s₀ (k + 1))
      = ψ.mapLanguage (LlocalInclusion s₀ k) := by
  rw [BoundedFormulaω.mapLanguage_mapLanguage, LlocalInclusion_comp_LlocalHom]

/-- **Constructor inversion for `mapLanguage` at `⋁`**: language maps preserve constructor heads,
so a `⋁`-image comes from a `⋁`-preimage, componentwise. Feeds the colimit component-membership
lemmas below. -/
private theorem BoundedFormulaω.mapLanguage_eq_iSup {L₁ L₂ : Language.{0, 0}} {g : L₁ →ᴸ L₂}
    {α : Type} {m : ℕ} {ψ : L₁.BoundedFormulaω α m} {φs : ℕ → L₂.BoundedFormulaω α m}
    (h : ψ.mapLanguage g = BoundedFormulaω.iSup φs) :
    ∃ ψs : ℕ → L₁.BoundedFormulaω α m,
      ψ = BoundedFormulaω.iSup ψs ∧ ∀ i, φs i = BoundedFormulaω.mapLanguage g (ψs i) := by
  cases ψ with
  | iSup ψs =>
    refine ⟨ψs, rfl, fun i => ?_⟩
    have h' : BoundedFormulaω.iSup (fun i => BoundedFormulaω.mapLanguage g (ψs i))
        = BoundedFormulaω.iSup φs := h
    injection h' with h1 h2
    exact (congrFun h2 i).symm
  | falsum => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | equal t₁ t₂ => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | rel R ts => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | imp φ₁ φ₂ => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | all φ₀ => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | iInf ψs => exact absurd h (by simp [BoundedFormulaω.mapLanguage])

/-- Constructor inversion for `mapLanguage` at `⋀`. -/
private theorem BoundedFormulaω.mapLanguage_eq_iInf {L₁ L₂ : Language.{0, 0}} {g : L₁ →ᴸ L₂}
    {α : Type} {m : ℕ} {ψ : L₁.BoundedFormulaω α m} {φs : ℕ → L₂.BoundedFormulaω α m}
    (h : ψ.mapLanguage g = BoundedFormulaω.iInf φs) :
    ∃ ψs : ℕ → L₁.BoundedFormulaω α m,
      ψ = BoundedFormulaω.iInf ψs ∧ ∀ i, φs i = BoundedFormulaω.mapLanguage g (ψs i) := by
  cases ψ with
  | iInf ψs =>
    refine ⟨ψs, rfl, fun i => ?_⟩
    have h' : BoundedFormulaω.iInf (fun i => BoundedFormulaω.mapLanguage g (ψs i))
        = BoundedFormulaω.iInf φs := h
    injection h' with h1 h2
    exact (congrFun h2 i).symm
  | falsum => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | equal t₁ t₂ => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | rel R ts => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | imp φ₁ φ₂ => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | all φ₀ => exact absurd h (by simp [BoundedFormulaω.mapLanguage])
  | iSup ψs => exact absurd h (by simp [BoundedFormulaω.mapLanguage])

/-- **Components of colimit-family disjunctions stay in the colimit family**: a `⋁` in
`ΓlocalColim` is the colimit image of a staged `⋁` (constructor inversion), whose components
reach the successor family by lift + subformula closure, hence the colimit family by the cocone
coherence. The membership plumbing that feeds the full-indiscernibility Ω-restoration at the
colimit family. -/
theorem iSup_component_mem_ΓlocalColim {m : ℕ}
    {φs : ℕ → (localColim s₀).BoundedFormulaω Empty m}
    (h : (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n)
      ∈ ΓlocalColim s₀) (i : ℕ) :
    (⟨m, φs i⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  obtain ⟨⟨n, ψ⟩, hpΓ, hpe⟩ := hk
  rw [show toLocalColimFormula s₀ k ⟨n, ψ⟩
      = ⟨n, ψ.mapLanguage (LlocalInclusion s₀ k)⟩ from rfl] at hpe
  obtain ⟨hn, h_snd⟩ := Sigma.mk.inj_iff.mp hpe
  subst hn
  obtain ⟨ψs, hψ, hcomp⟩ := BoundedFormulaω.mapLanguage_eq_iSup (eq_of_heq h_snd)
  subst hψ
  have hmem2 : (⟨n, ((ψs i).mapLanguage (LlocalHom s₀ k)).mapLanguage
        (LlocalInclusion s₀ (k + 1))⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ :=
    toLocalColimFormula_mem_ΓlocalColim s₀
      (bfSubformulas_subset_Γlocal_succ s₀ (liftGamma_mem_Γlocal_succ s₀ hpΓ)
        (Set.mem_range_self i))
  rw [mapLanguage_LlocalInclusion_lift s₀] at hmem2
  rw [hcomp i]
  exact hmem2

/-- Components of colimit-family conjunctions stay in the colimit family. -/
theorem iInf_component_mem_ΓlocalColim {m : ℕ}
    {φs : ℕ → (localColim s₀).BoundedFormulaω Empty m}
    (h : (⟨m, BoundedFormulaω.iInf φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n)
      ∈ ΓlocalColim s₀) (i : ℕ) :
    (⟨m, φs i⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  obtain ⟨⟨n, ψ⟩, hpΓ, hpe⟩ := hk
  rw [show toLocalColimFormula s₀ k ⟨n, ψ⟩
      = ⟨n, ψ.mapLanguage (LlocalInclusion s₀ k)⟩ from rfl] at hpe
  obtain ⟨hn, h_snd⟩ := Sigma.mk.inj_iff.mp hpe
  subst hn
  obtain ⟨ψs, hψ, hcomp⟩ := BoundedFormulaω.mapLanguage_eq_iInf (eq_of_heq h_snd)
  subst hψ
  have hmem2 : (⟨n, ((ψs i).mapLanguage (LlocalHom s₀ k)).mapLanguage
        (LlocalInclusion s₀ (k + 1))⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ :=
    toLocalColimFormula_mem_ΓlocalColim s₀
      (bfSubformulas_subset_Γlocal_succ s₀ (liftGamma_mem_Γlocal_succ s₀ hpΓ)
        (Set.mem_range_self i))
  rw [mapLanguage_LlocalInclusion_lift s₀] at hmem2
  rw [hcomp i]
  exact hmem2

/-- **Stage-agnostic readiness**: every stage-`k` family member — including the raw seed stage
`0`, where subformula closure is not available — is `TLReadyStage`-ready, by lifting one stage
(along `LlocalHom`, via `liftGamma_mem_Γlocal_succ`) and rewriting the colimit image back down
with the cocone coherence `mapLanguage_LlocalInclusion_lift`. -/
theorem LocalEMContext.TLReadyStage_of_Γlocal
    (ctx : LocalEMContext (localColim s₀) J (M := M)) {k : ℕ}
    (hclosed : LocalEMContext.DeFormClosedForColim (s₀ := s₀) (J := J) ctx)
    {n : ℕ} (ψ : (Llocal s₀ k).BoundedFormulaω Empty n)
    (hψ : (⟨n, ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) (S : Finset J)
    (hcov : ∀ i, locJSupport (localColim s₀) J (ts i) ⊆ S) :
    LocalEMContext.TLReadyStage s₀ J ctx k ψ ts S := by
  intro T hT
  rw [← mapLanguage_LlocalInclusion_lift]
  exact LocalEMContext.TLReady_mapLang_of_Γlocal_succ s₀ J ctx hclosed
    (ψ.mapLanguage (LlocalHom s₀ k)) (liftGamma_mem_Γlocal_succ s₀ hψ) ts T
    (fun i => (hcov i).trans hT)

end StagedReadiness

/-! ## The staged truth lemma (over a source model)

The load-bearing endpoint: over a source model `[s₀.Lang.Structure M]` with
`letI := localColimStructure s₀` in the statements (the `locSkWitness_universal` pattern — the
`all` case consumes the Skolem transport, which holds only for the concrete colimit structure).
`exists_localEMContext` uses the same `letI` pattern but lives downstream in `LocalEMExtraction`
and is **not** used or imported here. -/

section StagedTruthLemma

variable (s₀ : LocalStage) (J : Type) [LinearOrder J] {M : Type} [(localColim s₀).Structure M]

/-- **The staged local truth lemma, generic core**: over ANY `localColim` structure on the source
satisfying the Skolem-universality mixin `LocalSkolemUniversalForColim` — the schema term model
supplies a non-canonical instance. For a **successor-stage** family formula
`ψ ∈ Γlocal s₀ (k + 1)`, realizing its colimit image in the local EM term model on term-classes
is equivalent to its eventual deep truth. Structural induction on `ψ` threading the family
membership (each case derives its subformulas' memberships via
`bfSubformulas_subset_Γlocal_succ`): atoms/connectives via the layer-1 kernel (`mapLanguage`
distributes definitionally), `iSup`/`iInf` via `hc : ctx.OmegaComplete`, and the `all` case via
the Skolem-witness transport — the witness `locSkWitnessTerm` is keyed by the `.all` membership
`hmem` itself, has support `⊆ S`, and support-uniform readiness supplies the body's readiness at
every enlarged support. The Skolem step is discharged by the mixin
(`locSkWitness_universal_of_mixin`); the canonical wrapper below restores the original inline
form. Local analogue of `EMContext.truthLemmaStage`.

The completeness input is the **restricted** `OmegaCompleteForColim`: the `iSup`/`iInf` cases
consume it only at the colimit images of family members, whose memberships the induction
threads (global `OmegaComplete` users go through `OmegaComplete.toOmegaCompleteOn`). -/
theorem LocalEMContext.truthLemmaStage_of_skolemUniversal
    (hsk : LocalSkolemUniversalForColim s₀ (M := M)) :
    ∀ (ctx : LocalEMContext (localColim s₀) J (M := M)),
      LocalEMContext.OmegaCompleteForColim s₀ J ctx →
      ∀ (k : ℕ) {n : ℕ} (ψ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n),
        (⟨n, ψ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) ∈ Γlocal s₀ (k + 1) →
        ∀ (ts : Fin n → (localColim s₀)[[J]].Term Empty) (S : Finset J),
          (∀ i, locJSupport (localColim s₀) J (ts i) ⊆ S) →
          LocalEMContext.TLReadyStage s₀ J ctx (k + 1) ψ ts S →
          (@BoundedFormulaω.Realize ((localColim s₀)[[J]]) ctx.Carrier ctx.structure Empty n
              ((ψ.mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
                (lhomWithConstants (localColim s₀) J))
              Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
            LocalEMContext.eventualDeepTruth (Λ := localColim s₀) (J := J) ctx
              (ψ.mapLanguage (LlocalInclusion s₀ (k + 1))) ts S) := by
  intro ctx hc k
  let : (localColim s₀)[[J]].Structure ctx.Carrier := ctx.structure
  intro n ψ
  induction ψ with
  | falsum =>
    intro _ ts S _ _
    simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.realize_falsum,
      LocalEMContext.eventualDeepTruth_falsum_iff]
  | equal t₁ t₂ =>
    intro _ ts S hsub _
    have hbi : (Finset.univ.biUnion fun i => locJSupport (localColim s₀) J (ts i)) ⊆ S :=
      Finset.biUnion_subset.mpr fun i _ => hsub i
    exact LocalEMContext.eventualDeepTruth_equal_iff (Λ := localColim s₀) (J := J) ctx
      ((LlocalInclusion s₀ (k + 1)).onTerm t₁) ((LlocalInclusion s₀ (k + 1)).onTerm t₂) ts
      (Finset.union_subset
        ((locJSupport_onTerm_subst_subset (localColim s₀) J
          ((LlocalInclusion s₀ (k + 1)).onTerm t₁) ts).trans hbi)
        ((locJSupport_onTerm_subst_subset (localColim s₀) J
          ((LlocalInclusion s₀ (k + 1)).onTerm t₂) ts).trans hbi))
  | rel R args =>
    intro _ ts S hsub _
    have hbi : (Finset.univ.biUnion fun i => locJSupport (localColim s₀) J (ts i)) ⊆ S :=
      Finset.biUnion_subset.mpr fun i _ => hsub i
    exact LocalEMContext.eventualDeepTruth_rel_iff (Λ := localColim s₀) (J := J) ctx
      ((LlocalInclusion s₀ (k + 1)).onRelation R)
      (fun i => (LlocalInclusion s₀ (k + 1)).onTerm (args i)) ts
      (Finset.biUnion_subset.mpr fun i _ =>
        (locJSupport_onTerm_subst_subset (localColim s₀) J
          ((LlocalInclusion s₀ (k + 1)).onTerm (args i)) ts).trans hbi)
  | imp φ ψ ihφ ihψ =>
    intro hmem ts S hsub hready
    have hφmem : (⟨_, φ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_insert _ _)
    have hψmem : (⟨_, ψ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_insert_of_mem _ rfl)
    have hdec := (hready S (le_refl S)).1
    simp only [BoundedFormulaω.mapLanguage_imp]
    rw [LocalEMContext.eventualDeepTruth_imp_iff (Λ := localColim s₀) (J := J) ctx
      (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) φ)
      (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ)
      ts S hdec, BoundedFormulaω.realize_imp]
    exact imp_congr (ihφ hφmem ts S hsub fun T hT => (hready T hT).2.1)
      (ihψ hψmem ts S hsub fun T hT => (hready T hT).2.2)
  | iSup φs ih =>
    intro hmem ts S hsub hready
    rw [show ((BoundedFormulaω.iSup φs).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) J)
        = BoundedFormulaω.iSup (fun i => (BoundedFormulaω.mapLanguage
            (LlocalInclusion s₀ (k + 1)) (φs i)).mapLanguage
              (lhomWithConstants (localColim s₀) J)) from rfl,
      BoundedFormulaω.realize_iSup]
    constructor
    · rintro ⟨i, hi⟩
      exact LocalEMContext.eventualDeepTruth_iSup_of_exists (Λ := localColim s₀) (J := J) ctx
        (fun i => BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φs i)) ts S
        ⟨i, (ih i (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self i)) ts S hsub
          fun T hT => (hready T hT) i).mp hi⟩
    · intro h
      obtain ⟨i, hi⟩ := hc.iSup_complete
        (fun i => BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φs i))
        (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts S hsub h
      exact ⟨i, (ih i (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self i)) ts S hsub
        fun T hT => (hready T hT) i).mpr hi⟩
  | iInf φs ih =>
    intro hmem ts S hsub hready
    rw [show ((BoundedFormulaω.iInf φs).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) J)
        = BoundedFormulaω.iInf (fun i => (BoundedFormulaω.mapLanguage
            (LlocalInclusion s₀ (k + 1)) (φs i)).mapLanguage
              (lhomWithConstants (localColim s₀) J)) from rfl,
      BoundedFormulaω.realize_iInf]
    constructor
    · intro h
      exact hc.iInf_complete (fun i => BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k +
        1)) (φs i))
        (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts S hsub
        fun i => (ih i (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self i)) ts S hsub
          fun T hT => (hready T hT) i).mp (h i)
    · intro h i
      exact (ih i (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self i)) ts S hsub
        fun T hT => (hready T hT) i).mpr
        (LocalEMContext.eventualDeepTruth_iInf_forall (Λ := localColim s₀) (J := J) ctx
          (fun i => BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φs i)) ts S h i)
  | all ψ₀ ih =>
    intro hmem ts S hsub hready
    set φ₀ := BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ₀ with hφ₀
    -- the two membership uses: `hmem` (the `.all` member) keys the witness API; the body
    -- membership feeds the IH
    have hbodymem : (⟨_, ψ₀⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hmem rfl
    have hwS : locJSupport (localColim s₀) J (locSkWitnessTerm s₀ J hmem ts) ⊆ S := by
      rw [locJSupport_locSkWitnessTerm]; exact Finset.biUnion_subset.mpr fun i _ => hsub i
    have hsnoc : ∀ (u : (localColim s₀)[[J]].Term Empty) (i : Fin (_ + 1)),
        locJSupport (localColim s₀) J
            ((Fin.snoc ts u : Fin _ → (localColim s₀)[[J]].Term Empty) i)
          ⊆ S ∪ locJSupport (localColim s₀) J u := by
      intro u i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact Finset.subset_union_right
      · rw [Fin.snoc_castSucc]; exact (hsub j).trans Finset.subset_union_left
    have hsnocw : ∀ i, locJSupport (localColim s₀) J
        ((Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts) :
            Fin _ → (localColim s₀)[[J]].Term Empty) i) ⊆ S := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hwS
      · rw [Fin.snoc_castSucc]; exact hsub j
    -- support-uniform body readiness at every `snoc ts u` over `S ∪ locJSupport u`
    have hbody : ∀ (u : (localColim s₀)[[J]].Term Empty),
        LocalEMContext.TLReadyStage s₀ J ctx (k + 1) ψ₀ (Fin.snoc ts u)
          (S ∪ locJSupport (localColim s₀) J u) := by
      intro u T' hT'
      have h := (hready T' (Finset.subset_union_left.trans hT')) u
      rwa [Finset.union_eq_left.mpr (Finset.subset_union_right.trans hT')] at h
    have hready_wS : LocalEMContext.TLReadyStage s₀ J ctx (k + 1) ψ₀
        (Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts)) S := by
      have h := hbody (locSkWitnessTerm s₀ J hmem ts)
      rwa [Finset.union_eq_left.mpr hwS] at h
    -- witness bridge: `eDT (∀φ₀)` over any `T` ↔ body `eDT` at the witness
    have hwit : ∀ (T : Finset J),
        LocalEMContext.eventualDeepTruth (Λ := localColim s₀) (J := J) ctx φ₀
            (Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts)) T ↔
          LocalEMContext.eventualDeepTruth (Λ := localColim s₀) (J := J) ctx
            (BoundedFormulaω.all φ₀) ts T := by
      intro T
      rw [LocalEMContext.eventualDeepTruth, LocalEMContext.eventualDeepTruth]
      refine Filter.eventually_congr (Filter.Eventually.of_forall fun d => ?_)
      rw [BoundedFormulaω.realize_all, locDeepInterp_snoc]
      exact ⟨fun hd => locSkWitness_universal_of_mixin s₀ J hsk ctx.a d T hmem ts hd,
        fun hd => hd (locDeepInterp (localColim s₀) J ctx.a d T (locSkWitnessTerm s₀ J hmem ts))⟩
    have hinst : ∀ (T : Finset J) (u : (localColim s₀)[[J]].Term Empty),
        LocalEMContext.eventualDeepTruth (Λ := localColim s₀) (J := J) ctx
            (BoundedFormulaω.all φ₀) ts T →
          LocalEMContext.eventualDeepTruth (Λ := localColim s₀) (J := J) ctx φ₀
            (Fin.snoc ts u) T := by
      intro T u h
      rw [LocalEMContext.eventualDeepTruth] at h ⊢
      refine h.mono fun d hd => ?_
      rw [locDeepInterp_snoc]
      rw [BoundedFormulaω.realize_all] at hd
      exact hd (locDeepInterp (localColim s₀) J ctx.a d T u)
    rw [show ((BoundedFormulaω.all ψ₀).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) J)
        = BoundedFormulaω.all (φ₀.mapLanguage (lhomWithConstants (localColim s₀) J)) from rfl,
      BoundedFormulaω.realize_all]
    constructor
    · intro hcar
      have hcarw := hcar (ctx.mkClass (t := locSkWitnessTerm s₀ J hmem ts))
      rw [LocalEMContext.mkClass_snoc (Λ := localColim s₀) (J := J) ctx ts
        (locSkWitnessTerm s₀ J hmem ts)] at hcarw
      exact (hwit S).mp
        ((ih hbodymem (Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts)) S hsnocw hready_wS).mp hcarw)
    · intro heDT
      refine Quotient.ind (fun u => ?_)
      change (φ₀.mapLanguage (lhomWithConstants (localColim s₀) J)).Realize Empty.elim
          (Fin.snoc (fun i => ctx.mkClass (t := ts i)) (ctx.mkClass (t := u)))
      rw [LocalEMContext.mkClass_snoc (Λ := localColim s₀) (J := J) ctx ts u]
      have hready_wSj : LocalEMContext.TLReadyStage s₀ J ctx (k + 1) ψ₀
          (Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts))
          (S ∪ locJSupport (localColim s₀) J u) :=
        fun T' hT' => hready_wS T' (Finset.subset_union_left.trans hT')
      have hsnocwj : ∀ i, locJSupport (localColim s₀) J
          ((Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts) :
              Fin _ → (localColim s₀)[[J]].Term Empty) i)
            ⊆ S ∪ locJSupport (localColim s₀) J u :=
        fun i => (hsnocw i).trans Finset.subset_union_left
      have hcarw := (ih hbodymem (Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts)) S hsnocw
        hready_wS).mpr ((hwit S).mpr heDT)
      have hwT : LocalEMContext.eventualDeepTruth (Λ := localColim s₀) (J := J) ctx
          (BoundedFormulaω.all φ₀) ts (S ∪ locJSupport (localColim s₀) J u) :=
        (hwit (S ∪ locJSupport (localColim s₀) J u)).mp
          ((ih hbodymem (Fin.snoc ts (locSkWitnessTerm s₀ J hmem ts))
            (S ∪ locJSupport (localColim s₀) J u) hsnocwj hready_wSj).mp hcarw)
      exact (ih hbodymem (Fin.snoc ts u) (S ∪ locJSupport (localColim s₀) J u) (hsnoc u)
        (hbody u)).mpr (hinst (S ∪ locJSupport (localColim s₀) J u) u hwT)

/-- **Stage-agnostic lift corollary, generic core**: the staged truth lemma for an *original*
stage-`k` family member, at any stage including the raw seed stage `0`, over any mixin-satisfying
structure. Lifts the member one stage (along `LlocalHom`, via `liftGamma_mem_Γlocal_succ`) where
subformula closure is available, then rewrites the colimit image back down with the cocone
coherence `mapLanguage_LlocalInclusion_lift`. -/
theorem LocalEMContext.truthLemmaStage_of_mem_of_skolemUniversal
    (hsk : LocalSkolemUniversalForColim s₀ (M := M)) :
    ∀ (ctx : LocalEMContext (localColim s₀) J (M := M)),
      LocalEMContext.OmegaCompleteForColim s₀ J ctx →
      ∀ (k : ℕ) {n : ℕ} (ψ : (Llocal s₀ k).BoundedFormulaω Empty n),
        (⟨n, ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k →
        ∀ (ts : Fin n → (localColim s₀)[[J]].Term Empty) (S : Finset J),
          (∀ i, locJSupport (localColim s₀) J (ts i) ⊆ S) →
          LocalEMContext.TLReadyStage s₀ J ctx k ψ ts S →
          (@BoundedFormulaω.Realize ((localColim s₀)[[J]]) ctx.Carrier ctx.structure Empty n
              ((ψ.mapLanguage (LlocalInclusion s₀ k)).mapLanguage
                (lhomWithConstants (localColim s₀) J))
              Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
            LocalEMContext.eventualDeepTruth (Λ := localColim s₀) (J := J) ctx
              (ψ.mapLanguage (LlocalInclusion s₀ k)) ts S) := by
  intro ctx hc k n ψ hmem ts S hsub hready
  have hready' : LocalEMContext.TLReadyStage s₀ J ctx (k + 1)
      (ψ.mapLanguage (LlocalHom s₀ k)) ts S := by
    intro T hT
    rw [mapLanguage_LlocalInclusion_lift]
    exact hready T hT
  have h := LocalEMContext.truthLemmaStage_of_skolemUniversal s₀ J hsk ctx hc k
    (ψ.mapLanguage (LlocalHom s₀ k)) (liftGamma_mem_Γlocal_succ s₀ hmem) ts S hsub hready'
  rwa [mapLanguage_LlocalInclusion_lift] at h

end StagedTruthLemma

/-! ### Canonical wrappers (the original theorem names, over `localColimStructure`) -/

section StagedTruthLemmaCanonical

variable (s₀ : LocalStage) (J : Type) [LinearOrder J] {M : Type} [s₀.Lang.Structure M] [Nonempty M]

end StagedTruthLemmaCanonical

end FirstOrder.Language
