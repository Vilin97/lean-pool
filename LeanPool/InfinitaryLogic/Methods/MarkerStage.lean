/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Sort
import Mathlib.SetTheory.Cardinal.Regular
import LeanPool.InfinitaryLogic.Combinatorics.FiniteArityErdosRadoInduction
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
import LeanPool.InfinitaryLogic.Methods.Henkin.Construction
/-!
# The Marker stage: finite-fragment support extraction and Erdős–Rado certification

First layer of the template/consistency-property reshape of the Morley–Hanf chain (the
replacement for the ZFC-refutable in-`M` extraction ladder — see the audit fences on
`PureColoringHypothesis`/`MorleyHanfExtraction` in `Conditional/MorleyHanfTransfer.lean`).
Following Marker, *Lectures on Infinitary Model Theory* §5.2, the consistency-property route
certifies each **finite** fragment of an `L'[[J]]` template/constant theory by a large
homogeneous set in the source model, with the indiscernible sequence materializing only in
the model built by Model Existence.

This file provides the syntactic/combinatorial bridge between "finite fragment of a
constant theory" and "finite-arity Erdős–Rado approximation":

* a finite fragment is presented by its **index data** — a finite family of pairs
  `(fml p : L'.BoundedFormulaω Empty (ar p), tup p : Fin (ar p) ↪o J)` (per the template
  machinery in `Methods/EM/Realization.lean`, membership in a template theory carries
  exactly this witness data, so no syntactic support extraction is ever needed);
* `exists_markerSupport_factor` — collect the finite `J`-constant support of the family,
  enumerate it as `enum : Fin k ↪o J`, and factor every `tup p` through `enum`
  (via `exists_orderEmbedding_factor`);
* `markerStage_homogeneous` — pull the family back to a single arity-`k` truth-vector
  coloring over the source model and apply `finiteArityHomogeneousUpTo_beth_stage`:
  for every `α < ω₁`, a source of size `≥ ℶ_{ω₁}` yields a `(ℶ_α)⁺`-suborder on which the
  truth vector of the whole fragment is tuple-independent.

The per-`α` conclusion (available for **every** `α < ω₁` at once) is the Marker schedule.

## Layer 2: the certification predicates and their closure calculus

Toward the Marker consistency property, this file also provides the candidate member
predicate and its easy closure lemmas:

* `sentenceJConsts` — the syntactic `J`-constant support of an `L'[[J]]`-sentence (a `Set J`
  carved out of `functionsIn`; only countable in general, finite exactly for the sentences
  the construction certifies — support finiteness is *demanded* by the predicate, never
  computed);
* `MarkerFiniteCert M α F` — a finite set of sentences is certified at level `α`: a common
  finite support `S`, a `(ℶ_α)⁺`-suborder `e` of `M`, and satisfaction of every member under
  every constant interpretation that is increasing on `S` into `e`'s range;
* `MarkerCofinalConsistent M Sset` — every finite subset is certified at cofinally many
  `α < ω₁` (finite character makes weakening and chain closure pleasant);
* the closure lemmas that need **no** uniform countable choice: weakening, chain closure,
  the `C0` pair (no falsum, no contradiction), `C2` (double negation), `C3` (conjunction
  components), `C4'` (negated-disjunction components) — each by replacing the derived
  sentence with its trigger inside the certified fragment
  (`MarkerCofinalConsistent.extend_of_semantic`) and pushing pointwise `realize` lemmas
  through the same interpretations;
* `exists_uniform_of_cofinal_countable` — the `ω₁`-pigeonhole engine (ω₁ is regular, so a
  countably-colored cofinal α-schedule has a monochromatic cofinal subschedule);
* `MarkerISupUniform` — **the stated hard test**: does `⋁ᵢ φᵢ ∈ Sset` yield ONE disjunct
  `k` with `Sset ∪ {φs k}` still cofinally consistent? Per finite fragment `F` and level
  `α`, re-homogenization + the pigeonhole produce `k(F)`; the open question is uniformizing
  over ALL finite `F ⊆ Sset` — a directed intersection of antitone nonempty subsets of `ℕ`,
  which is NOT automatic. If provable, `markerConsistencyPropertyEq` is mostly assembly; if
  not, the fallback is a finite-member consistency notion with its own Henkin/model-existence
  adapter (the existing `ConsistencyPropertyEq` API also demands `extension` for ARBITRARY
  sentences, which certification cannot supply for sentences of infinite support — another
  reason the finite-member adapter may be the honest endpoint).

**C7/Henkin witness design (SETTLED: Henkin constant expansion — see Layer 3):** over a
relational `L'`, the closed `L'[[J]]`-terms are exactly the `J`-constants, so quantifier
witnesses must be fresh constants; a fresh `J`-constant would have to occupy a specific
order-position that an arbitrary linear `J` need not offer, so witnesses live in a separate
layer `(L'[[J]])[[ℕ]]` instead (`henkinConst`, `henkinConstsIn`, `expJConstsIn`), with the
reduct lemma (`Theoryω.model_reduct_of_expansion`) returning the final model to `L'[[J]]`.
The finite-member predicates over the expansion (`MarkerHenkinCert`,
`MarkerHenkinConsistent`, Layer 5) avoid the arbitrary-set `extension` field and the global
`C4` uniformization entirely — the Henkin construction consumes finite members along its
enumeration, per the classical Marker/Keisler shape. The `realizeWith` API (Layer 4)
confines all structure instances to two definition bodies; every closure rule is stated
through it. The choice-free closure rules (`C0`/`C1'`/`C2`/`C3`/`C4'`) are proved in
Layer 5; remaining: the re-homogenization rules (`C1`, `C3'`, `C4` — per-member
branch/index choice by coloring support tuples inside the certificate), `C7` via a fresh
witness index (enabled by the finite-Henkin-support invariant — see the Layer 5 audit
note), then the Henkin construction/model-existence adapter decision.
-/

universe u

namespace FirstOrder.Language

open Cardinal

/-- Every finite ordinal step stays below `ω₁`: if `α < ω₁` then `α + n < ω₁` for every
natural `n` — the room the Marker `α`-schedule uses to absorb per-fragment ladder costs. -/
theorem add_natCast_lt_omega_one {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) :
    ∀ n : ℕ, α + (n : Ordinal) < Ordinal.omega 1
  | 0 => by simpa using hα
  | (n + 1) => by
    have hn : α + (n : Ordinal) < Ordinal.omega 1 := add_natCast_lt_omega_one hα n
    have : α + ((n + 1 : ℕ) : Ordinal) = Order.succ (α + (n : Ordinal)) := by
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← Order.succ_eq_add_one]
    rw [this]
    exact (Cardinal.isSuccLimit_omega 1).succ_lt hn

/-- **Support factorization for a finite constant-fragment.** Given a finite family of
`J`-constant tuples `tup p : Fin (ar p) ↪o J` (the index data of a finite fragment of an
`L'[[J]]` constant theory), collect the finite support, enumerate it in increasing order as
`enum : Fin k ↪o J`, and factor every tuple through the enumeration. The range equation
identifies `enum` with the exact constant support of the fragment. -/
theorem exists_markerSupport_factor {J : Type u} [LinearOrder J]
    {m : ℕ} {ar : Fin m → ℕ} (tup : ∀ p, Fin (ar p) ↪o J) :
    ∃ (k : ℕ) (enum : Fin k ↪o J) (r : ∀ p, Fin (ar p) ↪o Fin k),
      (∀ p, (r p).trans enum = tup p) ∧
      Set.range ⇑enum = ⋃ p, Set.range ⇑(tup p) := by
  classical
  set S : Finset J := Finset.univ.biUnion fun p => Finset.univ.image ⇑(tup p) with hS
  have hrange : Set.range ⇑(S.orderEmbOfFin rfl) = ↑S := Finset.range_orderEmbOfFin S rfl
  have hmem : ∀ p (i : Fin (ar p)), tup p i ∈ Set.range ⇑(S.orderEmbOfFin rfl) := by
    intro p i
    rw [hrange]
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_univ p, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
  choose r hr using fun p =>
    exists_orderEmbedding_factor (S.orderEmbOfFin rfl) (tup p) (hmem p)
  refine ⟨S.card, S.orderEmbOfFin rfl, r, hr, ?_⟩
  rw [hrange]
  simp [hS]

/-- **The Marker-stage Erdős–Rado certification.** A finite fragment of an `L'[[J]]`
constant theory, presented by its index data `(fml p, tup p)`, pulls back along the support
factorization to a single arity-`k` truth-vector coloring over the source model `M`; for
every `α < ω₁`, `finiteArityHomogeneousUpTo_beth_stage` then yields a `(ℶ_α)⁺`-suborder of
`M` on which the truth of every formula of the fragment (at its own positions `r p` inside
the support) is independent of the choice of increasing `k`-tuple.

This is the per-fragment certification of the Marker consistency property: available at
every `α < ω₁` simultaneously (the cofinal schedule), from the single hypothesis
`|M| ≥ ℶ_{ω₁}` — per-`α`, per-finite-fragment approximations, never one `ω₁`-suborder
homogeneous for all arities at once (that jump is ZFC-refutable; see the audit fences). -/
theorem markerStage_homogeneous {L' : Language.{0, 0}} (M : Type) [L'.Structure M]
    [LinearOrder M] [WellFoundedLT M]
    (hM : Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1))
    (α : Ordinal.{0}) (hα : α < Ordinal.omega 1)
    {J : Type} [LinearOrder J]
    {m : ℕ} {ar : Fin m → ℕ} (fml : ∀ p : Fin m, L'.BoundedFormulaω Empty (ar p))
    (tup : ∀ p, Fin (ar p) ↪o J) :
    ∃ (k : ℕ) (enum : Fin k ↪o J) (r : ∀ p, Fin (ar p) ↪o Fin k),
      (∀ p, (r p).trans enum = tup p) ∧
      Set.range ⇑enum = ⋃ p, Set.range ⇑(tup p) ∧
      ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
        ∀ u u' : Fin k ↪o M,
          (∀ i, u i ∈ Set.range e) → (∀ i, u' i ∈ Set.range e) →
          ∀ p, ((fml p).Realize (Empty.elim : Empty → M) (⇑u ∘ ⇑(r p)) ↔
            (fml p).Realize (Empty.elim : Empty → M) (⇑u' ∘ ⇑(r p))) := by
  classical
  obtain ⟨k, enum, r, hr, hrange⟩ := exists_markerSupport_factor tup
  refine ⟨k, enum, r, hr, hrange, ?_⟩
  -- The truth-vector coloring at the support arity, defaulted elsewhere.
  let realColor : (Fin k ↪o M) → (Fin m → Prop) := fun u p =>
    (fml p).Realize (Empty.elim : Empty → M) (⇑u ∘ ⇑(r p))
  let c : ∀ n, (Fin n ↪o M) → (Fin m → Prop) :=
    Function.update (fun _ _ _ => True) k realColor
  have hc : c k = realColor := Function.update_self _ _ _
  have hsize : Cardinal.beth (α + ((2 * k + 2 : ℕ) : Ordinal)) ≤ Cardinal.mk M :=
    (Cardinal.beth_le_beth.mpr (add_natCast_lt_omega_one hα (2 * k + 2)).le).trans hM
  have hC : ∀ n : ℕ, Cardinal.mk (Fin m → Prop) ≤ Cardinal.beth α := fun _ =>
    (Cardinal.mk_lt_aleph0 (α := Fin m → Prop)).le.trans (Cardinal.aleph0_le_beth α)
  obtain ⟨e, he⟩ :=
    finiteArityHomogeneousUpTo_beth_stage α k hsize (fun _ => Fin m → Prop) hC c
  refine ⟨e, fun u u' hu hu' p => ?_⟩
  have h : c k u = c k u' := he k le_rfl u u' hu hu'
  have h' : realColor u = realColor u' := by rw [← hc]; exact h
  exact iff_of_eq (congrFun h' p)

/-! ## Layer 2: the certification predicates -/

section Certification

variable {L' : Language.{0, 0}} {J : Type}

-- `sentenceJConsts` and its monotonicity calculus (`_not`, `_component_iInf`,
-- `_component_iSup`, `_imp_left`, `_imp_right`) now live in `Methods/ConstantSupport.lean`,
-- the neutral home of the constant-support calculus (imported above). This section consumes
-- them unchanged.

variable [LinearOrder J] (M : Type) [L'.Structure M] [LinearOrder M]

/-- **The per-level Marker certification of a finite fragment**: a common finite constant
support `S`, a `(ℶ_α)⁺`-suborder `e` of the (well-ordered) source `M`, and satisfaction of
every member sentence under every constant interpretation that is strictly increasing on
`S` with values in the range of `e`. This is Marker's "`ℶ_α`-large set realizing `σ`",
stated semantically over interpretations so that the closure calculus needs no constructor
inversion through the template pipeline. -/
def MarkerFiniteCert (α : Ordinal.{0}) (F : Set L'[[J]].Sentenceω) : Prop :=
  ∃ S : Finset J, (∀ τ ∈ F, sentenceJConsts (L' := L') τ ⊆ ↑S) ∧
    ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
      ∀ σ : J → M, StrictMonoOn σ ↑S → (∀ j ∈ S, σ j ∈ Set.range e) →
        letI : (constantsOn J).Structure M := constantsOn.structure σ
        ∀ τ ∈ F, Sentenceω.Realize τ M

/-- **The candidate Marker member predicate**: every finite subfragment is certified at
cofinally many levels `α < ω₁`. Finite character makes weakening and chain closure direct;
the uniformization questions (`MarkerISupUniform` below) are exactly where it is honest. -/
def MarkerCofinalConsistent (Sset : Set L'[[J]].Sentenceω) : Prop :=
  ∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ Sset →
    ∀ β, β < Ordinal.omega 1 →
      ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧ MarkerFiniteCert M α F

variable {M}

/-- Certification is monotone (downward-closed) in the fragment. -/
theorem MarkerFiniteCert.mono {α : Ordinal.{0}} {F F' : Set L'[[J]].Sentenceω}
    (hFF : F' ⊆ F) (h : MarkerFiniteCert M α F) : MarkerFiniteCert M α F' := by
  obtain ⟨S, hsupp, e, hsat⟩ := h
  exact ⟨S, fun τ hτ => hsupp τ (hFF hτ), e,
    fun σ h1 h2 τ hτ => hsat σ h1 h2 τ (hFF hτ)⟩

/-- Cofinal consistency is monotone (downward-closed) in the sentence set. -/
theorem MarkerCofinalConsistent.mono {Sset Sset' : Set L'[[J]].Sentenceω}
    (hSS : Sset' ⊆ Sset) (h : MarkerCofinalConsistent M Sset) :
    MarkerCofinalConsistent M Sset' :=
  fun F hFin hsub => h F hFin (hsub.trans hSS)

/-- **Chain closure**: the union of a nonempty `⊆`-chain of cofinally consistent sets is
cofinally consistent — a finite subfragment of the union lies in one chain member. -/
theorem MarkerCofinalConsistent.sUnion_chain {chain : Set (Set L'[[J]].Sentenceω)}
    (hchain : ∀ T ∈ chain, MarkerCofinalConsistent M T)
    (hC : IsChain (· ⊆ ·) chain) (hne : chain.Nonempty) :
    MarkerCofinalConsistent M (⋃₀ chain) := by
  have key : ∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ ⋃₀ chain →
      ∃ T ∈ chain, F ⊆ T := by
    intro F hFin
    induction F, hFin using Set.Finite.induction_on with
    | empty =>
      intro _
      obtain ⟨T, hT⟩ := hne
      exact ⟨T, hT, Set.empty_subset T⟩
    | insert ha hs ih =>
      rename_i a s
      intro hsub
      obtain ⟨T₁, hT₁, hsT₁⟩ := ih fun x hx => hsub (Set.mem_insert_of_mem _ hx)
      obtain ⟨T₂, hT₂, haT₂⟩ := Set.mem_sUnion.mp (hsub (Set.mem_insert a s))
      rcases eq_or_ne T₁ T₂ with rfl | hne12
      · exact ⟨T₁, hT₁, Set.insert_subset_iff.mpr ⟨haT₂, hsT₁⟩⟩
      rcases hC.total hT₁ hT₂ with h12 | h21
      · exact ⟨T₂, hT₂, Set.insert_subset_iff.mpr ⟨haT₂, hsT₁.trans h12⟩⟩
      · exact ⟨T₁, hT₁, Set.insert_subset_iff.mpr ⟨h21 haT₂, hsT₁⟩⟩
  intro F hFin hsub β hβ
  obtain ⟨T, hT, hFT⟩ := key F hFin hsub
  exact hchain T hT F hFin hFT β hβ

/-- There is always an interpretation that is increasing on a given finite support into the
range of a `(ℶ_α)⁺`-suborder — the suborder's domain is infinite, so it contains increasing
tuples of every finite length. Supplies the "evaluation point" for the `C0` lemmas. -/
theorem exists_strictMonoOn_interp {α : Ordinal.{0}}
    (e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M) (S : Finset J) :
    ∃ σ : J → M, StrictMonoOn σ ↑S ∧ ∀ j ∈ S, σ j ∈ Set.range e := by
  classical
  have hinf : Infinite (Order.succ (Cardinal.beth α)).ord.ToType := by
    rw [Cardinal.infinite_iff, Cardinal.mk_ord_toType]
    exact (Cardinal.aleph0_le_beth α).trans (Order.le_succ _)
  obtain ⟨s, -, hcard⟩ :=
    (Set.infinite_univ (α := (Order.succ (Cardinal.beth α)).ord.ToType)).exists_subset_card_eq
      S.card
  refine ⟨fun j => if h : j ∈ S then e (s.orderEmbOfFin hcard ((S.orderIsoOfFin rfl).symm ⟨j, h⟩))
    else e (Classical.arbitrary _), ?_, ?_⟩
  · intro j hj j' hj' hlt
    dsimp only
    rw [dite_eq_left (Finset.mem_coe.mp hj), dite_eq_left (Finset.mem_coe.mp hj')]
    exact e.strictMono ((s.orderEmbOfFin hcard).strictMono
      ((S.orderIsoOfFin rfl).symm.strictMono (Subtype.mk_lt_mk.mpr hlt)))
  · intro j hj
    dsimp only
    rw [dite_eq_left hj]
    exact ⟨_, rfl⟩

/-- **`C0` (no falsum)**: a certified fragment cannot contain `⊥` — an increasing
interpretation exists and would have to realize it. -/
theorem MarkerFiniteCert.falsum_notMem {α : Ordinal.{0}} {F : Set L'[[J]].Sentenceω}
    (h : MarkerFiniteCert M α F) :
    (BoundedFormulaω.falsum : L'[[J]].Sentenceω) ∉ F := by
  intro hmem
  obtain ⟨S, hsupp, e, hsat⟩ := h
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  exact hsat σ hmono hrange _ hmem

/-- **`C0` (no contradiction)**: a certified fragment cannot contain both a sentence and
its negation. -/
theorem MarkerFiniteCert.not_mem_and_not_mem {α : Ordinal.{0}} {F : Set L'[[J]].Sentenceω}
    (h : MarkerFiniteCert M α F) (τ : L'[[J]].Sentenceω) : ¬(τ ∈ F ∧ τ.not ∈ F) := by
  rintro ⟨h1, h2⟩
  obtain ⟨S, hsupp, e, hsat⟩ := h
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  let : (constantsOn J).Structure M := constantsOn.structure σ
  exact (BoundedFormulaω.realize_not τ).mp (hsat σ hmono hrange _ h2)
    (hsat σ hmono hrange _ h1)

/-- **The semantic extension scheme** behind the choice-free closure conditions: if a
`trigger` sentence of `Sset` semantically entails a `new` sentence pointwise (under every
constant interpretation) and the constant support does not grow, then adjoining `new`
preserves cofinal consistency — inside any finite subfragment, replace `new` by its
trigger and reuse the certificate. -/
theorem MarkerCofinalConsistent.extend_of_semantic {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {trigger new : L'[[J]].Sentenceω}
    (hmem : trigger ∈ Sset)
    (hsupp : sentenceJConsts (L' := L') new ⊆ sentenceJConsts (L' := L') trigger)
    (hder : ∀ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      Sentenceω.Realize trigger M → Sentenceω.Realize new M) :
    MarkerCofinalConsistent M (Sset ∪ {new}) := by
  classical
  intro F hFin hsub β hβ
  by_cases hnew : new ∈ F
  · -- Replace `new` by `trigger` and re-certify.
    have hGfin : ((F \ {new}) ∪ {trigger}).Finite :=
      (hFin.subset Set.sdiff_subset).union (Set.finite_singleton _)
    have hGsub : (F \ {new}) ∪ {trigger} ⊆ Sset := by
      rintro τ (⟨hτF, hτne⟩ | hτ)
      · rcases hsub hτF with hS | h1
        · exact hS
        · exact absurd (Set.mem_singleton_iff.mp h1) hτne
      · rw [Set.mem_singleton_iff.mp hτ]
        exact hmem
    obtain ⟨α, hβα, hα, S, hsuppG, e, hsat⟩ := h _ hGfin hGsub β hβ
    have htrig : trigger ∈ (F \ {new}) ∪ {trigger} := Set.mem_union_right _ rfl
    refine ⟨α, hβα, hα, S, ?_, e, ?_⟩
    · intro τ hτ
      by_cases hτnew : τ = new
      · subst hτnew
        exact hsupp.trans (hsuppG trigger htrig)
      · exact hsuppG τ (Set.mem_union_left _ ⟨hτ, hτnew⟩)
    · intro σ h1 h2 τ hτ
      by_cases hτnew : τ = new
      · subst hτnew
        exact hder σ (hsat σ h1 h2 trigger htrig)
      · exact hsat σ h1 h2 τ (Set.mem_union_left _ ⟨hτ, hτnew⟩)
  · -- `new` unused: `F` already sits inside `Sset`.
    refine h F hFin (fun τ hτ => ?_) β hβ
    rcases hsub hτ with hS | h1
    · exact hS
    · rw [Set.mem_singleton_iff.mp h1] at hτ
      exact absurd hτ hnew

/-- **`C2` (double negation)**: `¬¬φ ∈ Sset` allows adjoining `φ`. -/
theorem MarkerCofinalConsistent.not_not {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {φ : L'[[J]].Sentenceω}
    (hmem : φ.not.not ∈ Sset) : MarkerCofinalConsistent M (Sset ∪ {φ}) :=
  h.extend_of_semantic hmem (by simp [sentenceJConsts_not]) fun σ => by
    let : (constantsOn J).Structure M := constantsOn.structure σ
    exact fun hreal => of_not_not fun hn =>
      (BoundedFormulaω.realize_not φ.not).mp hreal ((BoundedFormulaω.realize_not φ).mpr hn)

/-- **`C3` (conjunction components)**: `⋀ᵢ φᵢ ∈ Sset` allows adjoining every component. -/
theorem MarkerCofinalConsistent.iInf_component {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {φs : ℕ → L'[[J]].Sentenceω}
    (hmem : BoundedFormulaω.iInf φs ∈ Sset) (k : ℕ) :
    MarkerCofinalConsistent M (Sset ∪ {φs k}) :=
  h.extend_of_semantic hmem (sentenceJConsts_component_iInf φs k) fun σ => by
    let : (constantsOn J).Structure M := constantsOn.structure σ
    exact fun hreal => (BoundedFormulaω.realize_iInf φs).mp hreal k

/-- **`C4'` (negated-disjunction components)**: `¬⋁ᵢ φᵢ ∈ Sset` allows adjoining every
negated component. -/
theorem MarkerCofinalConsistent.neg_iSup_component {Sset : Set L'[[J]].Sentenceω}
    (h : MarkerCofinalConsistent M Sset) {φs : ℕ → L'[[J]].Sentenceω}
    (hmem : (BoundedFormulaω.iSup φs).not ∈ Sset) (k : ℕ) :
    MarkerCofinalConsistent M (Sset ∪ {(φs k).not}) :=
  h.extend_of_semantic hmem
    (by rw [sentenceJConsts_not, sentenceJConsts_not]
        exact sentenceJConsts_component_iSup φs k)
    fun σ => by
      let : (constantsOn J).Structure M := constantsOn.structure σ
      exact fun hreal => (BoundedFormulaω.realize_not (φs k)).mpr fun hk =>
        (BoundedFormulaω.realize_not _).mp hreal
          ((BoundedFormulaω.realize_iSup φs).mpr ⟨k, hk⟩)

end Certification

/-! ## The ω₁-pigeonhole engine and the stated uniformization test -/

/-- **The cofinal-schedule pigeonhole**: `ω₁` is regular, so if cofinally many levels below
`ω₁` each carry a witness from a countable index type, ONE index works cofinally. This is
the engine behind every uniformization step of the Marker consistency property (binary
choices such as `C1`, and — if it suffices — the disjunction choice `C4`). -/
theorem exists_uniform_of_cofinal_countable {K : Type} [Countable K]
    (P : Ordinal.{0} → K → Prop)
    (h : ∀ β, β < Ordinal.omega 1 → ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧ ∃ k, P α k) :
    ∃ k, ∀ β, β < Ordinal.omega 1 → ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧ P α k := by
  by_contra hcon
  push Not at hcon
  choose β hβlt hβ using hcon
  obtain ⟨α, hle, hα, k, hP⟩ := h (⨆ k, β k) (Ordinal.iSup_lt_omega_one hβlt)
  exact hβ k α ((Ordinal.le_iSup β k).trans hle) hα hP

variable {L' : Language.{0, 0}} {J : Type} [LinearOrder J]

/-- **The hard uniformization test** (deliberately a named statement, not a theorem): does
a disjunction in a cofinally consistent set admit ONE disjunct whose adjunction stays
cofinally consistent? Per finite subfragment `F` and level `α`, re-homogenizing the
disjunct index (countably many colors, `≤ ℶ_α`) and pigeonholing the cofinal schedule
(`exists_uniform_of_cofinal_countable`) produce a per-`F` disjunct `k(F)`; the open
content is uniformizing over ALL finite `F ⊆ Sset` — a directed intersection of antitone
nonempty subsets of `ℕ`, which is not automatic. If this holds, the Marker consistency
property (`ConsistencyPropertyEq`'s `C4_iSup`) is mostly assembly; if it fails, the honest
route is a finite-member consistency notion with its own Henkin/model-existence adapter
(see the module docstring, including the `extension`-field obstruction). -/
def MarkerISupUniform (M : Type) [L'.Structure M] [LinearOrder M] : Prop :=
  ∀ (Sset : Set L'[[J]].Sentenceω) (φs : ℕ → L'[[J]].Sentenceω),
    MarkerCofinalConsistent M Sset → BoundedFormulaω.iSup φs ∈ Sset →
    ∃ k, MarkerCofinalConsistent M (Sset ∪ {φs k})

/-! ## Layer 3: the Henkin-witness substrate

**C7 design decision (settled): Henkin constant expansion.** Quantifier witnesses live in a
separate `withConstants` layer `(L'[[J]])[[ℕ]]`, NOT among the `J`-constants: an arbitrary
linear `J` need not have an element in the order-gap a witness would require (and
`MorleySeedTailTemplateRealizable` quantifies over every linear `J`); a relational `L'`
provides no closed terms beyond constants, so witnesses cannot be generated internally; and
a separate layer keeps the EM skeleton (`J`, order-positioned, universally quantified in
certification) apart from proof-theoretic witnesses (`ℕ`, existentially interpreted per
skeleton interpretation). The finite-member consistency predicate lives over the expansion;
the endpoint returns to `L'[[J]]` by the reduct lemma. -/

section HenkinSubstrate

variable {L'' : Language.{0, 0}} {J : Type}

/-- The `n`-th Henkin witness constant of a constant expansion `L[[ℕ]]`, as a closed term. -/
def henkinConst {L : Language.{0, 0}} (n : ℕ) : (L[[ℕ]]).Term Empty :=
  Term.func (Sum.inr n : (L[[ℕ]]).Functions 0) Fin.elim0

/-- The Henkin-constant support of an expansion formula — the generalized `sentenceJConsts`
at base `L'[[J]]` and constant type `ℕ`. Freshness of a witness index `n` for a fragment
`F` is `∀ τ ∈ F, n ∉ henkinConstsIn τ`. -/
abbrev henkinConstsIn {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) : Set ℕ :=
  sentenceJConsts (L' := L''[[J]]) (J := ℕ) φ

/-- The `J`-constant support of an expansion formula: the `J`-constants sit inside the base
`L''[[J]]` layer, under `Sum.inl ∘ Sum.inr`. -/
def expJConstsIn {α : Type} {n : ℕ} (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) : Set J :=
  {j | (⟨0, (Sum.inl (Sum.inr j) : ((L''[[J]])[[ℕ]]).Functions 0)⟩ :
      Σ n, ((L''[[J]])[[ℕ]]).Functions n) ∈ BoundedFormulaω.functionsIn φ}

/-- **The forgetful/reduct lemma**: realizing the `mapLanguage`-image of an `L`-theory in a
constant-expansion structure yields, by reduct, a model of the original theory. The Henkin
construction will model the expanded theory over `(L'[[J]])[[ℕ]]`; the Marker endpoint
needs the `L'[[J]]` original. -/
theorem Theoryω.model_reduct_of_expansion {L : Language.{0, 0}} {γ : Type} (T : L.Theoryω)
    {N : Type} [L[[γ]].Structure N]
    (h : ∀ τ ∈ T,
      Sentenceω.Realize (BoundedFormulaω.mapLanguage (L.lhomWithConstants γ) τ) N) :
    letI : L.Structure N := (L.lhomWithConstants γ).reduct N
    Theoryω.Model T N := by
  let : L.Structure N := (L.lhomWithConstants γ).reduct N
  intro τ hτ
  exact (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants γ) τ _ _).mp (h τ hτ)

/-- Image form of the reduct lemma: a model of the pushed-forward theory reducts to a model
of the original. -/
theorem Theoryω.model_reduct_of_model_image {L : Language.{0, 0}} {γ : Type} (T : L.Theoryω)
    {N : Type} [L[[γ]].Structure N]
    (h : Theoryω.Model
      (BoundedFormulaω.mapLanguage (L.lhomWithConstants γ) '' T) N) :
    letI : L.Structure N := (L.lhomWithConstants γ).reduct N
    Theoryω.Model T N :=
  Theoryω.model_reduct_of_expansion T fun _ hτ => h _ (Set.mem_image_of_mem _ hτ)

-- (The finite-member predicates `MarkerHenkinCert`/`MarkerHenkinConsistent` live in
-- Layer 5 below, stated through the `realizeWith` API of Layer 4.)

end HenkinSubstrate

/-! ## Layer 4: the `realizeWith` evaluation API and the constant-agreement congruence

All structure instances are confined to the two wrapper definitions; every lemma statement
mentions only the wrappers, so no local-instance synthesis ever leaks into downstream
theorem statements. All later Marker closure rules are to be stated through this API. -/

section RealizeWith

variable {L'' : Language.{0, 0}} {J : Type} {M : Type} [L''.Structure M]

/-- Evaluation of an expansion term under a skeleton interpretation `σ : J → M` and a
Henkin interpretation `h : ℕ → M`. -/
def termValueWith (σ : J → M) (h : ℕ → M) {β : Type}
    (t : ((L''[[J]])[[ℕ]]).Term β) (v : β → M) : M :=
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  letI : (constantsOn ℕ).Structure M := constantsOn.structure h
  t.realize v

/-- Realization of an expansion formula under a skeleton interpretation `σ : J → M` and a
Henkin interpretation `h : ℕ → M`. -/
def realizeWith (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) : Prop :=
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  letI : (constantsOn ℕ).Structure M := constantsOn.structure h
  φ.Realize v xs

/-! ### Constructor unfolds (term level) -/

@[simp] theorem termValueWith_var (σ : J → M) (h : ℕ → M) {β : Type} (x : β) (v : β → M) :
    termValueWith (L'' := L'') σ h (Term.var x) v = v x := rfl

@[simp] theorem termValueWith_base (σ : J → M) (h : ℕ → M) {β : Type} {l : ℕ}
    (f : L''.Functions l) (ts : Fin l → ((L''[[J]])[[ℕ]]).Term β) (v : β → M) :
    termValueWith σ h (Term.func (Sum.inl (Sum.inl f)) ts) v =
      Structure.funMap f (fun i => termValueWith σ h (ts i) v) := rfl

@[simp] theorem termValueWith_skeleton (σ : J → M) (h : ℕ → M) {β : Type} (j : J)
    (ts : Fin 0 → ((L''[[J]])[[ℕ]]).Term β) (v : β → M) :
    termValueWith σ h
      (Term.func (Sum.inl (Sum.inr j) : ((L''[[J]])[[ℕ]]).Functions 0) ts) v = σ j := rfl

@[simp] theorem termValueWith_henkin (σ : J → M) (h : ℕ → M) {β : Type} (m : ℕ)
    (ts : Fin 0 → ((L''[[J]])[[ℕ]]).Term β) (v : β → M) :
    termValueWith σ h
      (Term.func (Sum.inr m : ((L''[[J]])[[ℕ]]).Functions 0) ts) v = h m := rfl

@[simp] theorem termValueWith_henkinConst (σ : J → M) (h : ℕ → M) (m : ℕ)
    (v : Empty → M) :
    termValueWith σ h (henkinConst (L := L''[[J]]) m) v = h m := rfl

/-! ### Constructor unfolds (formula level) -/

/-- The base relation symbol behind an expansion relation symbol (the constant layers add
no relations). -/
def baseRel {l : ℕ} : ((L''[[J]])[[ℕ]]).Relations l → L''.Relations l
  | Sum.inl (Sum.inl R) => R
  | Sum.inl (Sum.inr e) => e.elim
  | Sum.inr e => e.elim

@[simp] theorem realizeWith_falsum (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (v : α → M) (xs : Fin n → M) :
    realizeWith (L'' := L'') σ h BoundedFormulaω.falsum v xs ↔ False := Iff.rfl

@[simp] theorem realizeWith_equal (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (t₁ t₂ : ((L''[[J]])[[ℕ]]).Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.equal t₁ t₂) v xs ↔
      termValueWith σ h t₁ (Sum.elim v xs) = termValueWith σ h t₂ (Sum.elim v xs) :=
  Iff.rfl

@[simp] theorem realizeWith_rel (σ : J → M) (h : ℕ → M) {α : Type} {n l : ℕ}
    (R : ((L''[[J]])[[ℕ]]).Relations l) (ts : Fin l → ((L''[[J]])[[ℕ]]).Term (α ⊕ Fin n))
    (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.rel R ts) v xs ↔
      Structure.RelMap (baseRel (L'' := L'') R)
        (fun i => termValueWith σ h (ts i) (Sum.elim v xs)) := by
  rcases R with (R | e) | e
  · exact Iff.rfl
  · exact e.elim
  · exact e.elim

@[simp] theorem realizeWith_imp (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ ψ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (φ.imp ψ) v xs ↔ (realizeWith σ h φ v xs → realizeWith σ h ψ v xs) :=
  Iff.rfl

@[simp] theorem realizeWith_all (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α (n + 1)) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ.all v xs ↔ ∀ x, realizeWith σ h φ v (Fin.snoc xs x) := Iff.rfl

@[simp] theorem realizeWith_iSup (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.iSup φs) v xs ↔
      ∃ i, realizeWith σ h (φs i) v xs := Iff.rfl

@[simp] theorem realizeWith_iInf (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.iInf φs) v xs ↔
      ∀ i, realizeWith σ h (φs i) v xs := Iff.rfl

@[simp] theorem realizeWith_not (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ.not v xs ↔ ¬realizeWith σ h φ v xs := Iff.rfl

@[simp] theorem realizeWith_ex (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α (n + 1)) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ.ex v xs ↔ ∃ x, realizeWith σ h φ v (Fin.snoc xs x) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  let : (constantsOn ℕ).Structure M := constantsOn.structure h
  exact BoundedFormulaω.realize_ex φ

/-- Bridge to the raw sentence satisfaction used by `MarkerHenkinCert`. -/
theorem sentenceRealize_iff_realizeWith (σ : J → M) (h : ℕ → M)
    (τ : ((L''[[J]])[[ℕ]]).Sentenceω) :
    (letI : (constantsOn J).Structure M := constantsOn.structure σ
     letI : (constantsOn ℕ).Structure M := constantsOn.structure h
     Sentenceω.Realize τ M) ↔
    realizeWith σ h τ (Empty.elim : Empty → M) Fin.elim0 := Iff.rfl

/-! ### The constant-agreement congruence -/

/-- **Term congruence**: two skeleton interpretations agreeing on the occurring skeleton
constants and two Henkin interpretations agreeing on the occurring witness constants give
every term the same value. -/
theorem termValueWith_congr {σ σ' : J → M} {h h' : ℕ → M} {β : Type}
    (t : ((L''[[J]])[[ℕ]]).Term β)
    (hσ : ∀ j : J, (⟨0, (Sum.inl (Sum.inr j) : ((L''[[J]])[[ℕ]]).Functions 0)⟩ :
        Σ l, ((L''[[J]])[[ℕ]]).Functions l) ∈ Term.functionsIn t → σ j = σ' j)
    (hh : ∀ m : ℕ, (⟨0, (Sum.inr m : ((L''[[J]])[[ℕ]]).Functions 0)⟩ :
        Σ l, ((L''[[J]])[[ℕ]]).Functions l) ∈ Term.functionsIn t → h m = h' m)
    (v : β → M) :
    termValueWith σ h t v = termValueWith σ' h' t v := by
  induction t with
  | var x => rfl
  | @func l f ts ih =>
    have hmem : ∀ (i : Fin l) (s : Σ l, ((L''[[J]])[[ℕ]]).Functions l),
        s ∈ Term.functionsIn (ts i) → s ∈ Term.functionsIn (Term.func f ts) := by
      intro i s hs
      simp only [Term.functionsIn]
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_iUnion.mpr ⟨i, hs⟩))
    have hhead : (⟨l, f⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l) ∈
        Term.functionsIn (Term.func f ts) := by
      simp only [Term.functionsIn]
      exact Set.mem_insert _ _
    have hargs : ∀ i, termValueWith σ h (ts i) v = termValueWith σ' h' (ts i) v :=
      fun i => ih i (fun j hj => hσ j (hmem i _ hj)) (fun m hm => hh m (hmem i _ hm))
    rcases f with (f | c) | c
    · rw [termValueWith_base, termValueWith_base]
      exact congrArg _ (funext hargs)
    · cases l with
      -- `termValueWith_skeleton` is `rfl`, and its `j : J` cannot be unified with
      -- `c : (constantsOn J).Functions 0` at `implicit` transparency; `exact` checks at default.
      | zero => exact hσ c hhead
      | succ l => exact c.elim
    · cases l with
      | zero => exact hh c hhead
      | succ l => exact c.elim

/-- **Formula congruence** — the semantic-support engine of the Marker construction:
agreement on the occurring skeleton constants (`expJConstsIn`) and witness constants
(`henkinConstsIn`) gives identical realization. This is what makes tuple-canonical
colorings well-defined (`C4` re-homogenization) and fresh witness indices harmless
(`C7`). -/
theorem realizeWith_congr {σ σ' : J → M} {h h' : ℕ → M} {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n)
    (hσ : ∀ j ∈ expJConstsIn (L'' := L'') φ, σ j = σ' j)
    (hh : ∀ m ∈ henkinConstsIn (L'' := L'') φ, h m = h' m)
    (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ v xs ↔ realizeWith σ' h' φ v xs := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    rw [realizeWith_equal, realizeWith_equal,
      termValueWith_congr t₁
        (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn]
          exact Set.mem_union_left _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn]
          exact Set.mem_union_left _ hm)) _,
      termValueWith_congr t₂
        (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn]
          exact Set.mem_union_right _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn]
          exact Set.mem_union_right _ hm)) _]
  | rel R ts =>
    rw [realizeWith_rel, realizeWith_rel]
    exact iff_of_eq (congrArg _ (funext fun i =>
      termValueWith_congr (ts i)
        (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn]
          exact Set.mem_iUnion.mpr ⟨i, hj⟩))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn]
          exact Set.mem_iUnion.mpr ⟨i, hm⟩)) _))
  | imp φ ψ ihφ ihψ =>
    rw [realizeWith_imp, realizeWith_imp,
      ihφ (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_union_left _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_union_left _ hm)),
      ihψ (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_union_right _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_union_right _ hm))]
  | all φ ih =>
    rw [realizeWith_all, realizeWith_all]
    exact forall_congr' fun x => ih hσ hh (Fin.snoc xs x)
  | iSup φs ih =>
    rw [realizeWith_iSup, realizeWith_iSup]
    exact exists_congr fun i =>
      ih i (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_iUnion.mpr ⟨i, hj⟩))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_iUnion.mpr ⟨i, hm⟩)) xs
  | iInf φs ih =>
    rw [realizeWith_iInf, realizeWith_iInf]
    exact forall_congr' fun i =>
      ih i (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_iUnion.mpr ⟨i, hj⟩))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_iUnion.mpr ⟨i, hm⟩)) xs

end RealizeWith

-- The generic `functionsIn` structural calculus (relabel / castLE / subst / openBounds /
-- finiteness / subset-under-subst) now lives in `Methods/ConstantSupport.lean` (imported
-- above), the neutral home of the constant-support calculus. Consumed here unchanged.

/-! ## Layer 5: the finite Henkin closure calculus

**The freshness audit gate (settled by strengthening the predicate):** `henkinConstsIn` is
not automatically finite for an arbitrary `Lω₁ω` sentence — `iSup`/`iInf` can mention
countably many witness constants (e.g. `⋁ₙ (dₙ = dₙ)` has Henkin support all of `ℕ`) — so
"pick a fresh witness index outside the fragment's Henkin support" needs an invariant.
`MarkerHenkinCert` therefore carries a finite Henkin support `H : Finset ℕ` alongside the
skeleton support `S : Finset J`. The invariant is self-maintaining and non-restrictive:
the construction's seed sentences are `mapLanguage`-images of `L'[[J]]`-sentences (Henkin
support `∅`), and every closure operation shrinks the support (components, negations,
implication branches) or grows it by finitely many constants (substitution instances) —
an infinite-support sentence never enters a member of the Henkin enumeration. -/

section FiniteClosure

variable {L'' : Language.{0, 0}} {J : Type}

/-! ### Support lemmas for the expansion's skeleton constants -/

/-- Negation does not change the skeleton-constant support. -/
theorem expJConstsIn_not {α : Type} {n : ℕ} (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) :
    expJConstsIn (L'' := L'') φ.not = expJConstsIn (L'' := L'') φ := by
  ext j
  simp [expJConstsIn, BoundedFormulaω.functionsIn]

/-- A conjunction component's skeleton support is contained in the conjunction's. -/
theorem expJConstsIn_component_iInf {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (k : ℕ) :
    expJConstsIn (L'' := L'') (φs k) ⊆
      expJConstsIn (L'' := L'') (BoundedFormulaω.iInf φs) := by
  intro j hj
  simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_iUnion.mpr ⟨k, hj⟩

/-- A disjunction component's skeleton support is contained in the disjunction's. -/
theorem expJConstsIn_component_iSup {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (k : ℕ) :
    expJConstsIn (L'' := L'') (φs k) ⊆
      expJConstsIn (L'' := L'') (BoundedFormulaω.iSup φs) := by
  intro j hj
  simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_iUnion.mpr ⟨k, hj⟩

/-- An implication's antecedent skeleton support is contained in the implication's. -/
theorem expJConstsIn_imp_left {α : Type} {n : ℕ}
    (φ ψ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) :
    expJConstsIn (L'' := L'') φ ⊆ expJConstsIn (L'' := L'') (φ.imp ψ) := by
  intro j hj
  simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_union_left _ hj

/-- An implication's consequent skeleton support is contained in the implication's. -/
theorem expJConstsIn_imp_right {α : Type} {n : ℕ}
    (φ ψ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) :
    expJConstsIn (L'' := L'') ψ ⊆ expJConstsIn (L'' := L'') (φ.imp ψ) := by
  intro j hj
  simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_union_right _ hj

/-! ### Support lemmas for the expansion's Henkin constants (wrappers around the generic
`sentenceJConsts` family, restated so `rw` matches the `henkinConstsIn` spelling) -/

theorem henkinConstsIn_not {α : Type} {n : ℕ} (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) :
    henkinConstsIn (L'' := L'') φ.not = henkinConstsIn (L'' := L'') φ :=
  sentenceJConsts_not φ

theorem henkinConstsIn_component_iInf {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (k : ℕ) :
    henkinConstsIn (L'' := L'') (φs k) ⊆
      henkinConstsIn (L'' := L'') (BoundedFormulaω.iInf φs) :=
  sentenceJConsts_component_iInf φs k

theorem henkinConstsIn_component_iSup {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (k : ℕ) :
    henkinConstsIn (L'' := L'') (φs k) ⊆
      henkinConstsIn (L'' := L'') (BoundedFormulaω.iSup φs) :=
  sentenceJConsts_component_iSup φs k

theorem henkinConstsIn_imp_left {α : Type} {n : ℕ}
    (φ ψ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) :
    henkinConstsIn (L'' := L'') φ ⊆ henkinConstsIn (L'' := L'') (φ.imp ψ) :=
  sentenceJConsts_imp_left φ ψ

theorem henkinConstsIn_imp_right {α : Type} {n : ℕ}
    (φ ψ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) :
    henkinConstsIn (L'' := L'') ψ ⊆ henkinConstsIn (L'' := L'') (φ.imp ψ) :=
  sentenceJConsts_imp_right φ ψ

/-! ### The finite-member predicates -/

variable [LinearOrder J] (M : Type) [L''.Structure M] [LinearOrder M]

/-- **The certificate body at an explicit skeleton support `S`**: a `(ℶ_α)⁺`-suborder `e` of
the source, and — for EVERY skeleton interpretation increasing on `S` into `e`'s range —
SOME Henkin interpretation making every member true. The skeleton side stays universal (the
EM tuples); the witness side is existential per interpretation, because quantifier witnesses
vary with the tuple. The support-tracking conjuncts live in the wrapping predicates. -/
def MarkerHenkinBody (α : Ordinal.{0}) (S : Finset J)
    (F : Set ((L''[[J]])[[ℕ]].Sentenceω)) : Prop :=
  ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
    ∀ σ : J → M, StrictMonoOn σ ↑S → (∀ j ∈ S, σ j ∈ Set.range e) →
      ∃ h : ℕ → M, ∀ τ ∈ F, realizeWith σ h τ (Empty.elim : Empty → M) Fin.elim0

/-- **The per-level Henkin–Marker certification of a finite fragment** over the expansion
`(L''[[J]])[[ℕ]]`: a finite skeleton support `S`, a finite Henkin support `H` (the freshness
invariant), and a body at `S`. -/
def MarkerHenkinCert (α : Ordinal.{0}) (F : Set ((L''[[J]])[[ℕ]].Sentenceω)) : Prop :=
  ∃ (S : Finset J) (H : Finset ℕ),
    (∀ τ ∈ F, expJConstsIn (L'' := L'') τ ⊆ ↑S) ∧
    (∀ τ ∈ F, henkinConstsIn (L'' := L'') τ ⊆ ↑H) ∧
    MarkerHenkinBody M α S F

/-- **The finite-member consistency predicate**: a UNIFORM finite support `(S, H)` (fixed
across all levels — this is what the re-homogenization room lemma needs, and what the base
case `markerStage_homogeneous` naturally provides) together with certification bodies at
cofinally many levels below `ω₁`. The arbitrary-set `extension` field and the global `C4`
uniformization of the ambient `ConsistencyPropertyEq` API are deliberately avoided: the
Henkin construction consumes finite members along its enumeration, choosing disjuncts and
witnesses per member (the classical Marker/Keisler shape). -/
def MarkerHenkinConsistent (F : Finset ((L''[[J]])[[ℕ]].Sentenceω)) : Prop :=
  ∃ (S : Finset J) (H : Finset ℕ),
    (∀ τ ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)), expJConstsIn (L'' := L'') τ ⊆ ↑S) ∧
    (∀ τ ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)), henkinConstsIn (L'' := L'') τ ⊆ ↑H) ∧
    ∀ β, β < Ordinal.omega 1 →
      ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧
        MarkerHenkinBody M α S (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω))

variable {M}

/-- The body is monotone (downward-closed) in the fragment, at fixed support. -/
theorem MarkerHenkinBody.mono {α : Ordinal.{0}} {S : Finset J}
    {F F' : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hFF : F' ⊆ F)
    (hb : MarkerHenkinBody M α S F) : MarkerHenkinBody M α S F' := by
  obtain ⟨e, hsat⟩ := hb
  refine ⟨e, fun σ h1 h2 => ?_⟩
  obtain ⟨h, hh⟩ := hsat σ h1 h2
  exact ⟨h, fun τ hτ => hh τ (hFF hτ)⟩

/-- **Body-level semantic insertion**: if a `trigger` member semantically entails a `new`
sentence under every interpretation pair, adjoining `new` preserves the body (same suborder,
same witnesses). -/
theorem MarkerHenkinBody.insert_of_semantic {α : Ordinal.{0}} {S : Finset J}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hb : MarkerHenkinBody M α S F)
    {trigger new : (L''[[J]])[[ℕ]].Sentenceω} (hmem : trigger ∈ F)
    (hder : ∀ (σ : J → M) (h : ℕ → M),
      realizeWith σ h trigger (Empty.elim : Empty → M) Fin.elim0 →
      realizeWith σ h new (Empty.elim : Empty → M) Fin.elim0) :
    MarkerHenkinBody M α S (insert new F) := by
  obtain ⟨e, hsat⟩ := hb
  refine ⟨e, fun σ h1 h2 => ?_⟩
  obtain ⟨h, hh⟩ := hsat σ h1 h2
  refine ⟨h, ?_⟩
  rintro τ (rfl | hτ)
  · exact hder σ h (hh trigger hmem)
  · exact hh τ hτ

/-- Certification is monotone (downward-closed) in the fragment. -/
theorem MarkerHenkinCert.mono {α : Ordinal.{0}} {F F' : Set ((L''[[J]])[[ℕ]].Sentenceω)}
    (hFF : F' ⊆ F) (hc : MarkerHenkinCert M α F) : MarkerHenkinCert M α F' := by
  obtain ⟨S, H, hS, hH, hb⟩ := hc
  exact ⟨S, H, fun τ hτ => hS τ (hFF hτ), fun τ hτ => hH τ (hFF hτ), hb.mono hFF⟩

/-- Finite-member consistency is monotone (downward-closed). -/
theorem MarkerHenkinConsistent.mono {F F' : Finset ((L''[[J]])[[ℕ]].Sentenceω)}
    (hFF : F' ⊆ F) (h : MarkerHenkinConsistent M F) : MarkerHenkinConsistent M F' := by
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  have hFF' : (↑F' : Set ((L''[[J]])[[ℕ]].Sentenceω)) ⊆ ↑F := Finset.coe_subset.mpr hFF
  refine ⟨S, H, fun τ hτ => hS τ (hFF' hτ), fun τ hτ => hH τ (hFF' hτ), fun β hβ => ?_⟩
  obtain ⟨α, hβα, hα, hb⟩ := hcof β hβ
  exact ⟨α, hβα, hα, hb.mono hFF'⟩

/-- **The semantic insertion scheme** behind the choice-free closure rules: if a `trigger`
member semantically entails a `new` sentence under every interpretation pair, and neither
constant support grows, then adjoining `new` preserves certification — same supports, same
suborder, same witnesses. -/
theorem MarkerHenkinCert.insert_of_semantic {α : Ordinal.{0}}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hc : MarkerHenkinCert M α F)
    {trigger new : (L''[[J]])[[ℕ]].Sentenceω} (hmem : trigger ∈ F)
    (hJ : expJConstsIn (L'' := L'') new ⊆ expJConstsIn (L'' := L'') trigger)
    (hN : henkinConstsIn (L'' := L'') new ⊆ henkinConstsIn (L'' := L'') trigger)
    (hder : ∀ (σ : J → M) (h : ℕ → M),
      realizeWith σ h trigger (Empty.elim : Empty → M) Fin.elim0 →
      realizeWith σ h new (Empty.elim : Empty → M) Fin.elim0) :
    MarkerHenkinCert M α (insert new F) := by
  obtain ⟨S, H, hS, hH, hb⟩ := hc
  refine ⟨S, H, ?_, ?_, hb.insert_of_semantic hmem hder⟩
  · rintro τ (rfl | hτ)
    · exact hJ.trans (hS trigger hmem)
    · exact hS τ hτ
  · rintro τ (rfl | hτ)
    · exact hN.trans (hH trigger hmem)
    · exact hH τ hτ

/-- **`C0` (no falsum)**: a certified fragment cannot contain `⊥`. -/
theorem MarkerHenkinCert.falsum_notMem {α : Ordinal.{0}}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hc : MarkerHenkinCert M α F) :
    (BoundedFormulaω.falsum : (L''[[J]])[[ℕ]].Sentenceω) ∉ F := by
  intro hmem
  obtain ⟨S, H, hS, hH, e, hsat⟩ := hc
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  obtain ⟨h, hh⟩ := hsat σ hmono hrange
  exact (realizeWith_falsum σ h _ _).mp (hh _ hmem)

/-- **`C0` (no contradiction)**: a certified fragment cannot contain both a sentence and
its negation. -/
theorem MarkerHenkinCert.not_mem_and_not_mem {α : Ordinal.{0}}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hc : MarkerHenkinCert M α F)
    (τ : (L''[[J]])[[ℕ]].Sentenceω) : ¬(τ ∈ F ∧ τ.not ∈ F) := by
  rintro ⟨h1, h2⟩
  obtain ⟨S, H, hS, hH, e, hsat⟩ := hc
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  obtain ⟨h, hh⟩ := hsat σ hmono hrange
  exact (realizeWith_not σ h τ _ _).mp (hh _ h2) (hh _ h1)

open scoped Classical in
/-- The finite-member insertion scheme at the consistency level (uniform support preserved). -/
theorem MarkerHenkinConsistent.insert_of_semantic
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {trigger new : (L''[[J]])[[ℕ]].Sentenceω} (hmem : trigger ∈ F)
    (hJ : expJConstsIn (L'' := L'') new ⊆ expJConstsIn (L'' := L'') trigger)
    (hN : henkinConstsIn (L'' := L'') new ⊆ henkinConstsIn (L'' := L'') trigger)
    (hder : ∀ (σ : J → M) (hk : ℕ → M),
      realizeWith σ hk trigger (Empty.elim : Empty → M) Fin.elim0 →
      realizeWith σ hk new (Empty.elim : Empty → M) Fin.elim0) :
    MarkerHenkinConsistent M (insert new F) := by
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  have hmem' : trigger ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)) := Finset.mem_coe.mpr hmem
  refine ⟨S, H, ?_, ?_, fun β hβ => ?_⟩
  · rw [Finset.coe_insert]; rintro τ (rfl | hτ)
    · exact hJ.trans (hS trigger hmem')
    · exact hS τ hτ
  · rw [Finset.coe_insert]; rintro τ (rfl | hτ)
    · exact hN.trans (hH trigger hmem')
    · exact hH τ hτ
  · obtain ⟨α, hβα, hα, hb⟩ := hcof β hβ
    refine ⟨α, hβα, hα, ?_⟩
    rw [Finset.coe_insert]
    exact hb.insert_of_semantic hmem' hder

open scoped Classical in
/-- **`C2` (double negation)**: `¬¬φ ∈ F` allows adjoining `φ`. -/
theorem MarkerHenkinConsistent.not_not
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φ : (L''[[J]])[[ℕ]].Sentenceω} (hmem : φ.not.not ∈ F) :
    MarkerHenkinConsistent M (insert φ F) :=
  h.insert_of_semantic hmem
    (by simp [expJConstsIn_not]) (by simp [sentenceJConsts_not])
    fun σ hk hreal => of_not_not fun hn =>
      (realizeWith_not σ hk φ.not _ _).mp hreal ((realizeWith_not σ hk φ _ _).mpr hn)

open scoped Classical in
/-- **`C3` (conjunction components)**: `⋀ᵢ φᵢ ∈ F` allows adjoining every component. -/
theorem MarkerHenkinConsistent.iInf_component
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φs : ℕ → (L''[[J]])[[ℕ]].Sentenceω} (hmem : BoundedFormulaω.iInf φs ∈ F) (k : ℕ) :
    MarkerHenkinConsistent M (insert (φs k) F) :=
  h.insert_of_semantic hmem
    (expJConstsIn_component_iInf φs k) (sentenceJConsts_component_iInf φs k)
    fun σ hk hreal => (realizeWith_iInf σ hk φs _ _).mp hreal k

open scoped Classical in
/-- **`C4'` (negated-disjunction components)**: `¬⋁ᵢ φᵢ ∈ F` allows adjoining every
negated component. -/
theorem MarkerHenkinConsistent.neg_iSup_component
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φs : ℕ → (L''[[J]])[[ℕ]].Sentenceω} (hmem : (BoundedFormulaω.iSup φs).not ∈ F)
    (k : ℕ) : MarkerHenkinConsistent M (insert (φs k).not F) :=
  h.insert_of_semantic hmem
    (by rw [expJConstsIn_not, expJConstsIn_not]; exact expJConstsIn_component_iSup φs k)
    (by rw [henkinConstsIn_not, henkinConstsIn_not]
        exact henkinConstsIn_component_iSup φs k)
    fun σ hk hreal => (realizeWith_not σ hk (φs k) _ _).mpr fun hkk =>
      (realizeWith_not σ hk _ _ _).mp hreal ((realizeWith_iSup σ hk φs _ _).mpr ⟨k, hkk⟩)

open scoped Classical in
/-- **`C1'` (negated implication, antecedent)**: `¬(φ → ψ) ∈ F` allows adjoining `φ`. -/
theorem MarkerHenkinConsistent.neg_imp_left
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φ ψ : (L''[[J]])[[ℕ]].Sentenceω} (hmem : (φ.imp ψ).not ∈ F) :
    MarkerHenkinConsistent M (insert φ F) :=
  h.insert_of_semantic hmem
    (by rw [expJConstsIn_not]; exact expJConstsIn_imp_left φ ψ)
    (by rw [henkinConstsIn_not]; exact henkinConstsIn_imp_left φ ψ)
    fun σ hk hreal => of_not_not fun hφ =>
      (realizeWith_not σ hk (φ.imp ψ) _ _).mp hreal
        ((realizeWith_imp σ hk φ ψ _ _).mpr fun hp => absurd hp hφ)

open scoped Classical in
/-- **`C1'` (negated implication, consequent)**: `¬(φ → ψ) ∈ F` allows adjoining `¬ψ`. -/
theorem MarkerHenkinConsistent.neg_imp_right
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φ ψ : (L''[[J]])[[ℕ]].Sentenceω} (hmem : (φ.imp ψ).not ∈ F) :
    MarkerHenkinConsistent M (insert ψ.not F) :=
  h.insert_of_semantic hmem
    (by rw [expJConstsIn_not, expJConstsIn_not]; exact expJConstsIn_imp_right φ ψ)
    (by rw [henkinConstsIn_not, henkinConstsIn_not]
        exact henkinConstsIn_imp_right φ ψ)
    fun σ hk hreal => (realizeWith_not σ hk ψ _ _).mpr fun hψ =>
      (realizeWith_not σ hk (φ.imp ψ) _ _).mp hreal
        ((realizeWith_imp σ hk φ ψ _ _).mpr fun _ => hψ)

/-! ### Layer 5b engine: re-homogenization

The reusable machinery for the branch/index choice rules (`C1`, `C3'`, `C4`): color the
support tuples of a high-level certificate body by the branch a realizing interpretation
selects, re-homogenize inside the existing suborder via `finiteArityHomogeneousUpTo_beth_stage`
at a level lower by the finite ladder cost `2·|S|+2`, and read off a uniform branch. -/

section Rehomogenize

open Cardinal

variable {D : Type} [LinearOrder D]

/-- The skeleton interpretation determined by a source tuple `t : Fin S.card → D` and a
suborder `e : D ↪o M`: the `i`-th element of `S` maps to `e (t i)`, off `S` to a default. -/
noncomputable def tupleInterp (S : Finset J) (e : D ↪o M) (t : Fin S.card → D) (dflt : M) :
    J → M :=
  fun j => if h : j ∈ S then e (t ((S.orderIsoOfFin rfl).symm ⟨j, h⟩)) else dflt

theorem tupleInterp_orderEmbOfFin (S : Finset J) (e : D ↪o M) (t : Fin S.card → D) (dflt : M)
    (i : Fin S.card) : tupleInterp S e t dflt (S.orderEmbOfFin rfl i) = e (t i) := by
  have hmem : S.orderEmbOfFin rfl i ∈ S := S.orderEmbOfFin_mem rfl i
  rw [tupleInterp, dite_eq_left hmem]
  congr 2
  have hcoe : (⟨S.orderEmbOfFin rfl i, hmem⟩ : ↑S) = S.orderIsoOfFin rfl i :=
    Subtype.ext (S.coe_orderIsoOfFin_apply rfl i).symm
  rw [hcoe, OrderIso.symm_apply_apply]

theorem strictMonoOn_tupleInterp (S : Finset J) (e : D ↪o M) {t : Fin S.card → D}
    (ht : StrictMono t) (dflt : M) : StrictMonoOn (tupleInterp S e t dflt) ↑S := by
  intro j hj j' hj' hlt
  simp only [tupleInterp]
  rw [dite_eq_left (Finset.mem_coe.mp hj), dite_eq_left (Finset.mem_coe.mp hj')]
  exact e.strictMono (ht ((S.orderIsoOfFin rfl).symm.strictMono (Subtype.mk_lt_mk.mpr hlt)))

theorem tupleInterp_mem_range (S : Finset J) (e : D ↪o M) (t : Fin S.card → D) (dflt : M) :
    ∀ j ∈ S, tupleInterp S e t dflt j ∈ Set.range e := by
  intro j hj
  rw [tupleInterp, dite_eq_left hj]
  exact ⟨_, rfl⟩

/-- On the support, `tupleInterp` agrees with any `σ` matching it index-by-index. -/
theorem tupleInterp_eqOn (S : Finset J) (e : D ↪o M) (t : Fin S.card → D) (dflt : M)
    {σ : J → M} (h : ∀ i, e (t i) = σ (S.orderEmbOfFin rfl i)) :
    ∀ j ∈ S, tupleInterp S e t dflt j = σ j := by
  intro j hj
  have : j ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [S.range_orderEmbOfFin rfl]; exact hj
  obtain ⟨i, rfl⟩ := this
  rw [tupleInterp_orderEmbOfFin, h i]

/-- A finite tuple order-embedding into any infinite linear order exists. -/
theorem exists_orderEmb_fin {D : Type} [LinearOrder D] [Infinite D] (m : ℕ) :
    Nonempty (Fin m ↪o D) := by
  obtain ⟨s, -, hcard⟩ := (Set.infinite_univ (α := D)).exists_subset_card_eq m
  exact ⟨s.orderEmbOfFin hcard⟩

/-- **Support-tuple factoring**: an admissible `σ` for the composite suborder `e'.trans e`
factors through the support into a source tuple `t` landing in `Set.range e'` and matching
`σ` on `S` index-by-index. -/
theorem exists_factor_tuple {D₀ D : Type} [LinearOrder D₀] [LinearOrder D]
    (S : Finset J) (e : D ↪o M) (e' : D₀ ↪o D) {σ : J → M}
    (hmono : StrictMonoOn σ ↑S) (hrange : ∀ j ∈ S, σ j ∈ Set.range (e'.trans e)) :
    ∃ t : Fin S.card → D, StrictMono t ∧ (∀ i, t i ∈ Set.range e') ∧
      (∀ i, e (t i) = σ (S.orderEmbOfFin rfl i)) := by
  have hw : StrictMono (fun i => σ (S.orderEmbOfFin rfl i)) := fun i i' hii =>
    hmono (Finset.mem_coe.mpr (S.orderEmbOfFin_mem rfl i))
      (Finset.mem_coe.mpr (S.orderEmbOfFin_mem rfl i')) ((S.orderEmbOfFin rfl).strictMono hii)
  have hwrange : ∀ i, (OrderEmbedding.ofStrictMono _ hw) i ∈ Set.range (e'.trans e) :=
    fun i => hrange _ (S.orderEmbOfFin_mem rfl i)
  obtain ⟨s, hs⟩ := exists_orderEmbedding_factor (e'.trans e) (OrderEmbedding.ofStrictMono _ hw)
    hwrange
  refine ⟨fun i => e' (s i), e'.strictMono.comp s.strictMono, fun i => ⟨s i, rfl⟩, fun i => ?_⟩
  have hi := DFunLike.congr_fun hs i
  simpa [RelEmbedding.trans_apply] using hi

/-- **The re-homogenization engine.** From a certificate body of `F` at a level `α` exceeding
the target `α₀` by the finite ladder cost `2·|S|+2`, a covering branch family whose members
have skeleton support inside `S`, produce ONE branch `k` and a body of `insert (branch k) F`
at the target level `α₀`. The branch is uniform on the support tuples of the output suborder
(read off `finiteArityHomogeneousUpTo_beth_stage`); every admissible interpretation of the
output suborder factors through a support tuple, whose realizing interpretation selects
`branch k`, and constant-agreement congruence transfers realization back. -/
theorem MarkerHenkinBody.branch_choice
    {α₀ α : Ordinal.{0}} {S : Finset J} {F : Set ((L''[[J]])[[ℕ]].Sentenceω)}
    (hroom : α₀ + ((2 * S.card + 2 : ℕ) : Ordinal) ≤ α)
    (hb : MarkerHenkinBody M α S F)
    (hFsupp : ∀ τ ∈ F, expJConstsIn (L'' := L'') τ ⊆ ↑S)
    {K : Type} [Countable K] (branch : K → ((L''[[J]])[[ℕ]]).Sentenceω)
    (hbranchSupp : ∀ k, expJConstsIn (L'' := L'') (branch k) ⊆ ↑S)
    (hcover : ∀ (σ : J → M) (h : ℕ → M),
      (∀ τ ∈ F, realizeWith σ h τ (Empty.elim : Empty → M) Fin.elim0) →
      ∃ k, realizeWith σ h (branch k) (Empty.elim : Empty → M) Fin.elim0) :
    ∃ k, MarkerHenkinBody M α₀ S (insert (branch k) F) := by
  classical
  obtain ⟨e, hsat⟩ := hb
  -- The source order of the input suborder, and its infiniteness.
  set D := (Order.succ (Cardinal.beth α)).ord.ToType with hD
  have hDinf : Infinite D := by
    rw [hD, Cardinal.infinite_iff, Cardinal.mk_ord_toType]
    exact (Cardinal.aleph0_le_beth α).trans (Order.le_succ _)
  let dflt : M := e (Classical.arbitrary D)
  -- Every source tuple gives an admissible interpretation, hence a realizing `h` and a branch.
  have hadm : ∀ t : Fin S.card ↪o D, StrictMonoOn (tupleInterp S e ⇑t dflt) ↑S ∧
      ∀ j ∈ S, tupleInterp S e ⇑t dflt j ∈ Set.range e := fun t =>
    ⟨strictMonoOn_tupleInterp S e t.strictMono dflt, tupleInterp_mem_range S e ⇑t dflt⟩
  choose hOf hOf_spec using fun t : Fin S.card ↪o D =>
    hsat (tupleInterp S e ⇑t dflt) (hadm t).1 (hadm t).2
  choose colorFn colorFn_spec using fun t : Fin S.card ↪o D =>
    hcover (tupleInterp S e ⇑t dflt) (hOf t) (hOf_spec t)
  -- A canonical support tuple through the (soon-to-be) output suborder gives the uniform value.
  have hCK : Cardinal.mk K ≤ Cardinal.beth α₀ :=
    Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_beth α₀)
  have hI : Cardinal.beth (α₀ + ((2 * S.card + 2 : ℕ) : Ordinal)) ≤ Cardinal.mk D := by
    rw [hD, Cardinal.mk_ord_toType]
    exact (Cardinal.beth_le_beth.mpr hroom).trans (Order.le_succ _)
  obtain ⟨k₀t⟩ := exists_orderEmb_fin (D := D) S.card
  obtain ⟨e', he'⟩ := finiteArityHomogeneousUpTo_beth_stage α₀ S.card hI (fun _ => K)
    (fun _ => hCK) (Function.update (fun _ _ => colorFn k₀t) S.card colorFn)
  -- The uniform branch: the colour of any support tuple through `e'`.
  have hD0inf : Infinite (Order.succ (Cardinal.beth α₀)).ord.ToType := by
    rw [Cardinal.infinite_iff, Cardinal.mk_ord_toType]
    exact (Cardinal.aleph0_le_beth α₀).trans (Order.le_succ _)
  obtain ⟨tcan₀⟩ := exists_orderEmb_fin (D := (Order.succ (Cardinal.beth α₀)).ord.ToType) S.card
  set tcan : Fin S.card ↪o D := tcan₀.trans e' with htcan
  have hcupd : (Function.update (fun _ _ => colorFn k₀t) S.card colorFn) S.card = colorFn :=
    Function.update_self _ _ _
  refine ⟨colorFn tcan, e'.trans e, fun σ hσmono hσrange => ?_⟩
  -- Factor `σ` through `e'.trans e` into a source tuple `t` landing in `Set.range e'`.
  obtain ⟨tf, htf_mono, htf_range, htf_eq⟩ := exists_factor_tuple S e e' hσmono hσrange
  set t : Fin S.card ↪o D := OrderEmbedding.ofStrictMono tf htf_mono with ht
  have ht_range : ∀ i, t i ∈ Set.range e' := htf_range
  have htcan_range : ∀ i, tcan i ∈ Set.range e' := fun i => ⟨tcan₀ i, rfl⟩
  -- Homogeneity: the branch of `t` equals the branch of the canonical tuple.
  have hcol : colorFn t = colorFn tcan := by
    have h := he' S.card le_rfl t tcan ht_range htcan_range
    simpa only [Function.update_self] using h
  -- The realizing `h` for `t`, transferred from `tupleInterp` to `σ` by congruence.
  refine ⟨hOf t, ?_⟩
  have hagree : ∀ j ∈ S, tupleInterp S e ⇑t dflt j = σ j :=
    tupleInterp_eqOn S e ⇑t dflt fun i => htf_eq i
  rintro τ (rfl | hτ)
  · -- The new sentence `branch (colorFn tcan)`.
    rw [← hcol]
    exact (realizeWith_congr (branch (colorFn t))
      (fun c hc => hagree c (Finset.mem_coe.mp (hbranchSupp (colorFn t) hc)))
      (fun _ _ => rfl) _ _).mp (colorFn_spec t)
  · -- An old member `τ ∈ F`.
    exact (realizeWith_congr τ
      (fun c hc => hagree c (Finset.mem_coe.mp (hFsupp τ hτ hc)))
      (fun _ _ => rfl) _ _).mp (hOf_spec t τ hτ)

/-! ### Layer 5b-2: the branch/index choice rules -/

open scoped Classical in
/-- **Consistency-level branch choice** (re-homogenization + the `ω₁`-pigeonhole assembly):
a covering branch family for a `trigger ∈ F`, whose members' constant supports lie inside the
trigger's, yields ONE branch `k` with `insert (branch k) F` consistent. Per target level the
body comes from `MarkerHenkinBody.branch_choice` (asked at the ladder-cost-offset level, kept
below `ω₁` by `add_natCast_lt_omega_one`); the single uniform `k` comes from
`exists_uniform_of_cofinal_countable` (`ω₁` is regular). Uniform support `(S, H)` is preserved. -/
theorem MarkerHenkinConsistent.branch_choice
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {K : Type} [Countable K] (branch : K → (L''[[J]])[[ℕ]].Sentenceω)
    {trigger : (L''[[J]])[[ℕ]].Sentenceω} (hmem : trigger ∈ F)
    (hbJ : ∀ k, expJConstsIn (L'' := L'') (branch k) ⊆ expJConstsIn (L'' := L'') trigger)
    (hbN : ∀ k, henkinConstsIn (L'' := L'') (branch k) ⊆ henkinConstsIn (L'' := L'') trigger)
    (hcover : ∀ (σ : J → M) (hk : ℕ → M),
      realizeWith σ hk trigger (Empty.elim : Empty → M) Fin.elim0 →
      ∃ k, realizeWith σ hk (branch k) (Empty.elim : Empty → M) Fin.elim0) :
    ∃ k, MarkerHenkinConsistent M (insert (branch k) F) := by
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  have hmem' : trigger ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)) := Finset.mem_coe.mpr hmem
  have hbranchS : ∀ k, expJConstsIn (L'' := L'') (branch k) ⊆ ↑S :=
    fun k => (hbJ k).trans (hS trigger hmem')
  have hstep : ∀ β, β < Ordinal.omega 1 →
      ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧
        ∃ k, MarkerHenkinBody M α S (↑(insert (branch k) F) : Set ((L''[[J]])[[ℕ]].Sentenceω)) := by
    intro β hβ
    obtain ⟨α', hβ'α', hα', hbody⟩ :=
      hcof (β + ((2 * S.card + 2 : ℕ) : Ordinal)) (add_natCast_lt_omega_one hβ (2 * S.card + 2))
    obtain ⟨k, hk⟩ := hbody.branch_choice hβ'α' hS branch hbranchS
      (fun σ hσ hF => hcover σ hσ (hF trigger hmem'))
    exact ⟨β, le_rfl, hβ, k, by rwa [Finset.coe_insert]⟩
  obtain ⟨k, hk⟩ := exists_uniform_of_cofinal_countable
    (fun α k => MarkerHenkinBody M α S (↑(insert (branch k) F) : Set ((L''[[J]])[[ℕ]].Sentenceω)))
    hstep
  refine ⟨k, S, H, ?_, ?_, hk⟩
  · rw [Finset.coe_insert]; rintro τ (rfl | hτ)
    · exact (hbJ k).trans (hS trigger hmem')
    · exact hS τ hτ
  · rw [Finset.coe_insert]; rintro τ (rfl | hτ)
    · exact (hbN k).trans (hH trigger hmem')
    · exact hH τ hτ

open scoped Classical in
/-- **`C4` (disjunction witness)**: `⋁ᵢ φᵢ ∈ F` yields a uniform disjunct `k` with
`insert (φs k) F` consistent. -/
theorem MarkerHenkinConsistent.iSup_choice
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φs : ℕ → (L''[[J]])[[ℕ]].Sentenceω} (hmem : BoundedFormulaω.iSup φs ∈ F) :
    ∃ k, MarkerHenkinConsistent M (insert (φs k) F) :=
  h.branch_choice φs hmem (fun k => expJConstsIn_component_iSup φs k)
    (fun k => henkinConstsIn_component_iSup φs k)
    (fun σ hk hreal => (realizeWith_iSup σ hk φs _ _).mp hreal)

open scoped Classical in
/-- **`C3'` (negated-conjunction witness)**: `¬⋀ᵢ φᵢ ∈ F` yields a uniform index `k` with
`insert (φs k).not F` consistent. -/
theorem MarkerHenkinConsistent.neg_iInf_choice
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φs : ℕ → (L''[[J]])[[ℕ]].Sentenceω} (hmem : (BoundedFormulaω.iInf φs).not ∈ F) :
    ∃ k, MarkerHenkinConsistent M (insert (φs k).not F) := by
  refine h.branch_choice (fun k => (φs k).not) hmem
    (fun k => by rw [expJConstsIn_not, expJConstsIn_not]; exact expJConstsIn_component_iInf φs k)
    (fun k => by
      rw [henkinConstsIn_not, henkinConstsIn_not]; exact henkinConstsIn_component_iInf φs k)
    (fun σ hk hreal => ?_)
  rw [realizeWith_not, realizeWith_iInf, not_forall] at hreal
  obtain ⟨i, hi⟩ := hreal
  exact ⟨i, (realizeWith_not σ hk (φs i) _ _).mpr hi⟩

open scoped Classical in
/-- **`C1` (implication)**: `φ → ψ ∈ F` — one of `insert φ.not F`, `insert ψ F` is
consistent (the branch is chosen uniformly over the support tuples). -/
theorem MarkerHenkinConsistent.imp_choice
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φ ψ : (L''[[J]])[[ℕ]].Sentenceω} (hmem : φ.imp ψ ∈ F) :
    MarkerHenkinConsistent M (insert φ.not F) ∨ MarkerHenkinConsistent M (insert ψ F) := by
  obtain ⟨b, hb⟩ := h.branch_choice (fun b => cond b ψ φ.not) hmem
    (fun b => by cases b
                 · simpa only [Bool.cond_false, expJConstsIn_not] using expJConstsIn_imp_left φ ψ
                 · simpa only [Bool.cond_true] using expJConstsIn_imp_right φ ψ)
    (fun b => by cases b
                 · simpa only [Bool.cond_false, henkinConstsIn_not] using henkinConstsIn_imp_left φ ψ
                 · simpa only [Bool.cond_true] using henkinConstsIn_imp_right φ ψ)
    (fun σ hk hreal => by
      rw [realizeWith_imp] at hreal
      by_cases hφ : realizeWith σ hk φ (Empty.elim : Empty → M) Fin.elim0
      · exact ⟨true, hreal hφ⟩
      · exact ⟨false, (realizeWith_not σ hk φ _ _).mpr hφ⟩)
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

/-! ### Layer 5c: the Henkin witness rule (C7)

The one closure rule of a different shape: no re-homogenization, but a fresh Henkin constant.
From `∃x φ(x) ∈ F`, pick a witness index `n` outside the finite Henkin support `H`, update the
Henkin interpretation at `n` to the existential witness (per skeleton interpretation), and
adjoin the instance `φ(dₙ)`. The finite-support invariant is what makes "fresh `n`" available. -/

/-- The Henkin witness instance of an existential: `φ` with its last bound variable filled by
the `n`-th Henkin constant. -/
noncomputable def witnessSentence
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) (n : ℕ) : ((L''[[J]])[[ℕ]]).Sentenceω :=
  (φ.openBounds).subst (fun _ => henkinConst n)

omit [LinearOrder J] in
/-- `∃` does not change the mentioned function symbols. -/
theorem functionsIn_ex {α : Type} {m : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α (m + 1)) :
    BoundedFormulaω.functionsIn φ.ex = BoundedFormulaω.functionsIn φ := by
  simp [BoundedFormulaω.functionsIn]

omit [LinearOrder J] in
theorem expJConstsIn_ex (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) :
    expJConstsIn (L'' := L'') φ.ex = expJConstsIn (L'' := L'') φ := by
  simp only [expJConstsIn, functionsIn_ex]

omit [LinearOrder J] in
theorem henkinConstsIn_ex (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) :
    henkinConstsIn (L'' := L'') φ.ex = henkinConstsIn (L'' := L'') φ := by
  simp only [henkinConstsIn, sentenceJConsts, functionsIn_ex]

omit [LinearOrder J] in
/-- The witness constant `dₙ`'s only mentioned symbol is the `n`-th Henkin constant. -/
theorem functionsIn_henkinConst (n : ℕ) :
    (henkinConst (L := L''[[J]]) n).functionsIn ⊆
      {(⟨0, Sum.inr n⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l)} := by
  intro s hs
  simp only [henkinConst, Term.functionsIn] at hs
  rcases Set.mem_insert_iff.mp hs with h | h
  · exact h
  · rw [Set.mem_iUnion] at h; obtain ⟨i, _⟩ := h; exact i.elim0

omit [LinearOrder J] in
/-- The witness sentence adds no new function symbol beyond `φ`'s and the fresh constant `dₙ`. -/
theorem functionsIn_witnessSentence (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) (n : ℕ) :
    BoundedFormulaω.functionsIn (witnessSentence φ n) ⊆
      BoundedFormulaω.functionsIn φ ∪ {(⟨0, Sum.inr n⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l)} := by
  refine (BoundedFormulaω.functionsIn_subst _ _).trans ?_
  rw [BoundedFormulaω.functionsIn_openBounds]
  exact Set.union_subset_union_right _
    (Set.iUnion_subset fun _ => functionsIn_henkinConst n)

omit [LinearOrder J] in
theorem expJConstsIn_witnessSentence (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) (n : ℕ) :
    expJConstsIn (L'' := L'') (witnessSentence φ n) ⊆ expJConstsIn (L'' := L'') φ := by
  intro j hj
  rcases (functionsIn_witnessSentence φ n) hj with h | h
  · exact h
  -- Term mode: the goal spells `Sum.inr j` at the whnf'd type `J`, so it is not type-correct at
  -- `implicit` transparency and `simp` cannot discharge the disequality in place.
  · have heq : (⟨0, Sum.inl (Sum.inr j)⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l) = ⟨0, Sum.inr n⟩ :=
      Set.mem_singleton_iff.mp h
    have h2 : (Sum.inl (Sum.inr j) : ((L''[[J]])[[ℕ]]).Functions 0) = Sum.inr n :=
      eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    cases h2

omit [LinearOrder J] in
theorem henkinConstsIn_witnessSentence (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) (n : ℕ) :
    henkinConstsIn (L'' := L'') (witnessSentence φ n) ⊆
      insert n (henkinConstsIn (L'' := L'') φ) := by
  intro m hm
  rcases (functionsIn_witnessSentence φ n) hm with h | h
  · exact Set.mem_insert_of_mem _ h
  · have heq : (⟨0, Sum.inr m⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l) = ⟨0, Sum.inr n⟩ :=
      Set.mem_singleton_iff.mp h
    exact Set.mem_insert_iff.mpr
      (Or.inl (Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)))

omit [LinearOrder J] [LinearOrder M] in
/-- **The semantic bridge**: realizing the witness sentence is realizing `φ` with the last
bound variable set to the Henkin interpretation of `dₙ`. -/
theorem realizeWith_witness (σ : J → M) (h : ℕ → M)
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) (n : ℕ) :
    realizeWith σ h (witnessSentence φ n) (Empty.elim : Empty → M) Fin.elim0 ↔
      realizeWith σ h φ (Empty.elim : Empty → M) (Fin.snoc Fin.elim0 (h n)) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  let : (constantsOn ℕ).Structure M := constantsOn.structure h
  show ((φ.openBounds).subst (fun _ => henkinConst n)).Realize (Empty.elim : Empty → M) Fin.elim0 ↔
    φ.Realize (Empty.elim : Empty → M) (Fin.snoc Fin.elim0 (h n))
  rw [BoundedFormulaω.realize_subst]
  refine (realize_openBounds φ _).trans (iff_of_eq ?_)
  congr 1

/-- **Body-level `C7`**: from `∃x φ(x) ∈ F` and a Henkin index `n` fresh for `F`, the witness
instance can be adjoined — update the Henkin interpretation at `n` to the existential witness;
`n`'s freshness leaves every old member unchanged (`realizeWith_congr`). -/
theorem MarkerHenkinBody.witness {α : Ordinal.{0}} {S : Finset J}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hb : MarkerHenkinBody M α S F)
    {φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1} (hmem : φ.ex ∈ F) (n : ℕ)
    (hn : ∀ τ ∈ F, n ∉ henkinConstsIn (L'' := L'') τ) :
    MarkerHenkinBody M α S (insert (witnessSentence φ n) F) := by
  obtain ⟨e, hsat⟩ := hb
  refine ⟨e, fun σ hσmono hσrange => ?_⟩
  obtain ⟨h, hh⟩ := hsat σ hσmono hσrange
  have hex := hh φ.ex hmem
  rw [realizeWith_ex] at hex
  obtain ⟨x, hx⟩ := hex
  have hnφ : n ∉ henkinConstsIn (L'' := L'') φ := by
    rw [← henkinConstsIn_ex]; exact hn φ.ex hmem
  refine ⟨Function.update h n x, ?_⟩
  rintro τ (rfl | hτ)
  · rw [realizeWith_witness, Function.update_self]
    exact (realizeWith_congr φ (fun _ _ => rfl)
      (fun m hm => Function.update_of_ne (ne_of_mem_of_not_mem hm hnφ) x h) _ _).mpr hx
  · exact (realizeWith_congr τ (fun _ _ => rfl)
      (fun m hm => Function.update_of_ne (ne_of_mem_of_not_mem hm (hn τ hτ)) x h) _ _).mpr
      (hh τ hτ)

open scoped Classical in
/-- **`C7` (existential witness)**: `∃x φ(x) ∈ F` yields a fresh Henkin index `n` with
`insert (witnessSentence φ n) F` consistent — the new Henkin support is `insert n H`. -/
theorem MarkerHenkinConsistent.ex_witness
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    {φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1} (hmem : φ.ex ∈ F) :
    ∃ n, MarkerHenkinConsistent M (insert (witnessSentence φ n) F) := by
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  obtain ⟨n, hnH⟩ := Infinite.exists_notMem_finset H
  have hmem' : φ.ex ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)) := Finset.mem_coe.mpr hmem
  have hfresh : ∀ τ ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)), n ∉ henkinConstsIn (L'' := L'') τ :=
    fun τ hτ hnmem => hnH (Finset.mem_coe.mp (hH τ hτ hnmem))
  refine ⟨n, S, insert n H, ?_, ?_, fun β hβ => ?_⟩
  · rw [Finset.coe_insert]; rintro τ (rfl | hτ)
    · exact (expJConstsIn_witnessSentence φ n).trans
        ((expJConstsIn_ex φ) ▸ hS φ.ex hmem')
    · exact hS τ hτ
  · rw [Finset.coe_insert]; rintro τ (rfl | hτ)
    · refine (henkinConstsIn_witnessSentence φ n).trans ?_
      rw [Finset.coe_insert]
      exact Set.insert_subset_insert ((henkinConstsIn_ex φ) ▸ hH φ.ex hmem')
    · exact (hH τ hτ).trans (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
  · obtain ⟨α, hβα, hα, hbody⟩ := hcof β hβ
    refine ⟨α, hβα, hα, ?_⟩
    rw [Finset.coe_insert]
    exact hbody.witness hmem' n hfresh

end Rehomogenize

/-! ## Layer 6a: the finite-support universe and the restricted extension rule

The bespoke finite-Henkin adapter avoids the ambient `ConsistencyPropertyEq` (whose
`extension` field quantifies over ARBITRARY sentences, which Marker consistency cannot
supply at infinite constant-support). Instead it works over the sentences of finite constant
support — exactly the sentences the Marker recursion from the template seed ever produces —
and replaces the arbitrary-sentence `extension` field with a restricted extension rule proved
by the same Layer-5b re-homogenization engine (branch over `Bool`, colour support tuples by
whether `τ` is realized). -/

/-- A sentence of finite constant support: finitely many `J`-constants and finitely many
Henkin constants. The restricted universe the adapter decides over. -/
def HasFiniteConstSupport (τ : ((L''[[J]])[[ℕ]]).Sentenceω) : Prop :=
  ∃ (S : Finset J) (H : Finset ℕ),
    expJConstsIn (L'' := L'') τ ⊆ ↑S ∧ henkinConstsIn (L'' := L'') τ ⊆ ↑H

/-- The subtype of finite-constant-support sentences — the universe of the maximal
finite-support theory. -/
abbrev FSentence := {τ : ((L''[[J]])[[ℕ]]).Sentenceω // HasFiniteConstSupport (L'' := L'') τ}

omit [LinearOrder J] in
/-- Negation preserves finite constant support. -/
theorem HasFiniteConstSupport.not {τ : ((L''[[J]])[[ℕ]]).Sentenceω}
    (hτ : HasFiniteConstSupport (L'' := L'') τ) : HasFiniteConstSupport (L'' := L'') τ.not := by
  obtain ⟨S, H, hS, hH⟩ := hτ
  exact ⟨S, H, by rw [expJConstsIn_not]; exact hS, by rw [henkinConstsIn_not]; exact hH⟩

/-- A body over `S` is a body over any larger support (fewer admissible interpretations). -/
theorem MarkerHenkinBody.enlarge_support {α : Ordinal.{0}} {S S' : Finset J}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hSS : S ⊆ S') (hb : MarkerHenkinBody M α S F) :
    MarkerHenkinBody M α S' F := by
  obtain ⟨e, hsat⟩ := hb
  have hSS' : (↑S : Set J) ⊆ ↑S' := Finset.coe_subset.mpr hSS
  exact ⟨e, fun σ hσmono hσrange => hsat σ
    (fun a ha b hb hab => hσmono (hSS' ha) (hSS' hb) hab) (fun j hj => hσrange j (hSS hj))⟩

open scoped Classical in
/-- **The restricted extension rule** (the replacement for the ambient `extension` field):
any finite-constant-support sentence `τ` can be decided — one of `insert τ F`, `insert τ.not F`
is Marker-consistent. Enlarge the uniform support by `τ`'s finite supports, re-homogenize the
Boolean "is `τ` realized" colouring of the support tuples (`MarkerHenkinBody.branch_choice`,
covering is the unconditional tautology `τ ∨ ¬τ`), and uniformize the branch over the cofinal
`α`-schedule. -/
theorem MarkerHenkinConsistent.extension
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    (τ : ((L''[[J]])[[ℕ]]).Sentenceω) (hτ : HasFiniteConstSupport (L'' := L'') τ) :
    MarkerHenkinConsistent M (insert τ F) ∨ MarkerHenkinConsistent M (insert τ.not F) := by
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  obtain ⟨Sτ, Hτ, hSτ, hHτ⟩ := hτ
  set S' : Finset J := S ∪ Sτ with hS'def
  set H' : Finset ℕ := H ∪ Hτ with hH'def
  have hSS' : (↑S : Set J) ⊆ ↑S' := by rw [hS'def, Finset.coe_union]; exact Set.subset_union_left
  have hSτS' : (↑Sτ : Set J) ⊆ ↑S' := by rw [hS'def, Finset.coe_union]; exact Set.subset_union_right
  have hHH' : (↑H : Set ℕ) ⊆ ↑H' := by rw [hH'def, Finset.coe_union]; exact Set.subset_union_left
  have hHτH' : (↑Hτ : Set ℕ) ⊆ ↑H' := by rw [hH'def, Finset.coe_union]; exact Set.subset_union_right
  -- Branch support: both `τ` and `τ.not` are supported by `Sτ`.
  have hbJ : ∀ b : Bool, expJConstsIn (L'' := L'') (cond b τ.not τ) ⊆ ↑S' := by
    intro b; cases b
    · exact hSτ.trans hSτS'
    · rw [Bool.cond_true, expJConstsIn_not]; exact hSτ.trans hSτS'
  have hbH : ∀ b : Bool, henkinConstsIn (L'' := L'') (cond b τ.not τ) ⊆ ↑H' := by
    intro b; cases b
    · exact hHτ.trans hHτH'
    · rw [Bool.cond_true, henkinConstsIn_not]; exact hHτ.trans hHτH'
  -- The uniform choice over `Bool`, per target level via re-homogenization.
  have hstep : ∀ β, β < Ordinal.omega 1 →
      ∃ α, β ≤ α ∧ α < Ordinal.omega 1 ∧
        ∃ b : Bool, MarkerHenkinBody M α S'
          (↑(insert (cond b τ.not τ) F) : Set ((L''[[J]])[[ℕ]]).Sentenceω) := by
    intro β hβ
    obtain ⟨α', hβ'α', hα', hbody⟩ :=
      hcof (β + ((2 * S'.card + 2 : ℕ) : Ordinal)) (add_natCast_lt_omega_one hβ (2 * S'.card + 2))
    have hbody' : MarkerHenkinBody M α' S' (↑F : Set ((L''[[J]])[[ℕ]]).Sentenceω) :=
      hbody.enlarge_support (Finset.subset_union_left)
    obtain ⟨b, hb⟩ := hbody'.branch_choice hβ'α'
      (fun ρ hρ => (hS ρ hρ).trans hSS') (fun b => cond b τ.not τ) hbJ
      (fun σ hk _ => by
        by_cases hτr : realizeWith σ hk τ (Empty.elim : Empty → M) Fin.elim0
        · exact ⟨false, hτr⟩
        · exact ⟨true, (realizeWith_not σ hk τ _ _).mpr hτr⟩)
    exact ⟨β, le_rfl, hβ, b, by rwa [Finset.coe_insert]⟩
  obtain ⟨b, hb⟩ := exists_uniform_of_cofinal_countable
    (fun α b => MarkerHenkinBody M α S'
      (↑(insert (cond b τ.not τ) F) : Set ((L''[[J]])[[ℕ]]).Sentenceω)) hstep
  have hcons : MarkerHenkinConsistent M (insert (cond b τ.not τ) F) := by
    refine ⟨S', H', ?_, ?_, hb⟩
    · rw [Finset.coe_insert]; rintro ρ (rfl | hρ)
      · exact hbJ b
      · exact (hS ρ hρ).trans hSS'
    · rw [Finset.coe_insert]; rintro ρ (rfl | hρ)
      · exact hbH b
      · exact (hH ρ hρ).trans hHH'
  cases b
  · exact Or.inl hcons
  · exact Or.inr hcons

/-! ## Layer 6b: the equality closure rules (C5/C6)

The equality rules the term-model quotient and truth lemma will need on the restricted
maximal theory. Both are proved semantically (certification is realizability in `M`, whose
equality is genuine) via unconditional/entailed insertion, with finite constant support
tracked through the syntactic support API. -/

omit [LinearOrder J] in
/-- A sentence mentioning only finitely many function symbols has finite constant support:
`expJConstsIn`/`henkinConstsIn` are preimages of `functionsIn` under injective maps. -/
theorem HasFiniteConstSupport_of_functionsIn_finite {τ : ((L''[[J]])[[ℕ]]).Sentenceω}
    (hfin : (BoundedFormulaω.functionsIn τ).Finite) : HasFiniteConstSupport (L'' := L'') τ := by
  have hgexp : Function.Injective
      (fun j : J => (⟨0, Sum.inl (Sum.inr j)⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l)) := by
    intro a b hab; injection hab with _ h2; exact Sum.inr_injective (Sum.inl_injective h2)
  have hghen : Function.Injective
      (fun m : ℕ => (⟨0, Sum.inr m⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l)) := by
    intro a b hab; injection hab with _ h2; exact Sum.inr_injective h2
  refine ⟨(hfin.preimage hgexp.injOn).toFinset, (hfin.preimage hghen.injOn).toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]; exact subset_rfl
  · rw [Set.Finite.coe_toFinset]; exact subset_rfl

/-- **Body-level entailed insertion**: if the members of `F` semantically entail `new` under
every interpretation, adjoining `new` preserves the body (same suborder, same witnesses). -/
theorem MarkerHenkinBody.insert_of_entailed {α : Ordinal.{0}} {S : Finset J}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hb : MarkerHenkinBody M α S F)
    (new : ((L''[[J]])[[ℕ]]).Sentenceω)
    (hent : ∀ (σ : J → M) (hk : ℕ → M),
      (∀ ρ ∈ F, realizeWith σ hk ρ (Empty.elim : Empty → M) Fin.elim0) →
      realizeWith σ hk new (Empty.elim : Empty → M) Fin.elim0) :
    MarkerHenkinBody M α S (insert new F) := by
  obtain ⟨e, hsat⟩ := hb
  refine ⟨e, fun σ hm hr => ?_⟩
  obtain ⟨h, hh⟩ := hsat σ hm hr
  refine ⟨h, ?_⟩
  rintro ρ (rfl | hρ)
  · exact hent σ h hh
  · exact hh ρ hρ

open scoped Classical in
/-- **Consistency-level entailed insertion**: a finite-support sentence entailed by `F` (under
every interpretation) can be adjoined; the uniform support grows by the new sentence's finite
supports. No re-homogenization (the entailment is unconditional over the branch). -/
theorem MarkerHenkinConsistent.insert_entailed
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    (new : ((L''[[J]])[[ℕ]]).Sentenceω) (hnew : HasFiniteConstSupport (L'' := L'') new)
    (hent : ∀ (σ : J → M) (hk : ℕ → M),
      (∀ ρ ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)), realizeWith σ hk ρ
        (Empty.elim : Empty → M) Fin.elim0) →
      realizeWith σ hk new (Empty.elim : Empty → M) Fin.elim0) :
    MarkerHenkinConsistent M (insert new F) := by
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  obtain ⟨Snew, Hnew, hSnew, hHnew⟩ := hnew
  refine ⟨S ∪ Snew, H ∪ Hnew, ?_, ?_, fun β hβ => ?_⟩
  · rw [Finset.coe_insert]; rintro ρ (rfl | hρ)
    · exact hSnew.trans (Finset.coe_subset.mpr Finset.subset_union_right)
    · exact (hS ρ hρ).trans (Finset.coe_subset.mpr Finset.subset_union_left)
  · rw [Finset.coe_insert]; rintro ρ (rfl | hρ)
    · exact hHnew.trans (Finset.coe_subset.mpr Finset.subset_union_right)
    · exact (hH ρ hρ).trans (Finset.coe_subset.mpr Finset.subset_union_left)
  · obtain ⟨α, hβα, hα, hbody⟩ := hcof β hβ
    refine ⟨α, hβα, hα, ?_⟩
    rw [Finset.coe_insert]
    exact (hbody.enlarge_support Finset.subset_union_left).insert_of_entailed new hent

open scoped Classical in
/-- **`C5` (equality reflexivity)**: `t = t` can always be adjoined — it is valid, so any
realizing interpretation realizes it too. -/
theorem MarkerHenkinConsistent.eq_refl
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    (t : ((L''[[J]])[[ℕ]]).Term (Empty ⊕ Fin 0)) :
    MarkerHenkinConsistent M (insert (BoundedFormulaω.equal t t) F) := by
  refine h.insert_entailed (BoundedFormulaω.equal t t) ?_ (fun σ hk _ => ?_)
  · exact HasFiniteConstSupport_of_functionsIn_finite
      ((Term.functionsIn_finite t).union (Term.functionsIn_finite t))
  · rw [realizeWith_equal]

omit [LinearOrder J] [LinearOrder M] in
/-- The `C6` substitution instance mentions no symbol beyond the old instance `φ(t₁)` and the
equality sentence — the syntactic support bound behind `eq_subst`'s finite support. -/
theorem functionsIn_eq_subst_subset (t₁ t₂ : ((L''[[J]])[[ℕ]]).Term Empty)
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω (Fin 1) 0) :
    BoundedFormulaω.functionsIn (φ.subst (fun _ => t₂)) ⊆
      BoundedFormulaω.functionsIn (φ.subst (fun _ => t₁)) ∪
        BoundedFormulaω.functionsIn (BoundedFormulaω.equal
          (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
          (t₂.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) := by
  refine (BoundedFormulaω.functionsIn_subst (fun _ => t₂) φ).trans (Set.union_subset ?_ ?_)
  · exact (BoundedFormulaω.functionsIn_subset_subst (fun _ => t₁) φ).trans Set.subset_union_left
  · refine Set.iUnion_subset fun _ => ?_
    rw [← Term.functionsIn_relabel (Sum.inl : Empty → Empty ⊕ Fin 0) t₂]
    exact Set.subset_union_of_subset_right Set.subset_union_right _

omit [LinearOrder J] [LinearOrder M] in
/-- Realizing a relabel of a closed term is realizing the term (the extra bound slot is
vacuous). -/
theorem termValueWith_relabel_inl (σ : J → M) (hk : ℕ → M)
    (t : ((L''[[J]])[[ℕ]]).Term Empty) :
    termValueWith σ hk (t.relabel Sum.inl) (Sum.elim (Empty.elim : Empty → M) Fin.elim0)
      = termValueWith σ hk t (Empty.elim : Empty → M) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  let : (constantsOn ℕ).Structure M := constantsOn.structure hk
  show (t.relabel Sum.inl).realize (Sum.elim Empty.elim Fin.elim0) = t.realize Empty.elim
  rw [Term.realize_relabel]
  exact congrArg (fun v => Term.realize v t) (Subsingleton.elim _ _)

omit [LinearOrder J] [LinearOrder M] in
/-- The substitution-of-a-closed-term bridge: realizing `φ(t)` is realizing `φ` with its bound
variable set to the value of `t`. -/
theorem realizeWith_subst_const (σ : J → M) (hk : ℕ → M)
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω (Fin 1) 0) (t : ((L''[[J]])[[ℕ]]).Term Empty) :
    realizeWith σ hk (φ.subst (fun _ => t)) (Empty.elim : Empty → M) Fin.elim0 ↔
      realizeWith σ hk φ (fun _ => termValueWith σ hk t (Empty.elim : Empty → M)) Fin.elim0 := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  let : (constantsOn ℕ).Structure M := constantsOn.structure hk
  show (φ.subst (fun _ => t)).Realize Empty.elim Fin.elim0 ↔
    φ.Realize (fun _ => t.realize Empty.elim) Fin.elim0
  rw [BoundedFormulaω.realize_subst]

open scoped Classical in
/-- **`C6` (equality substitution)**: from `t₁ = t₂ ∈ F` and `φ(t₁) ∈ F`, the instance `φ(t₂)`
can be adjoined — the equality forces equal term values, and `realizeWith_subst_const`
transports `φ`. The support of `φ(t₂)` stays inside `F`'s uniform support
(`functionsIn_eq_subst_subset`). -/
theorem MarkerHenkinConsistent.eq_subst
    {F : Finset ((L''[[J]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    (t₁ t₂ : ((L''[[J]])[[ℕ]]).Term Empty) (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω (Fin 1) 0)
    (hmem_eq : BoundedFormulaω.equal (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      (t₂.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ F)
    (hmem_φ : φ.subst (fun _ => t₁) ∈ F) :
    MarkerHenkinConsistent M (insert (φ.subst (fun _ => t₂)) F) := by
  have hmem_eq' : BoundedFormulaω.equal (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      (t₂.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈
      (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)) := Finset.mem_coe.mpr hmem_eq
  have hmem_φ' : φ.subst (fun _ => t₁) ∈ (↑F : Set ((L''[[J]])[[ℕ]].Sentenceω)) :=
    Finset.mem_coe.mpr hmem_φ
  have hnew : HasFiniteConstSupport (L'' := L'') (φ.subst (fun _ => t₂)) := by
    obtain ⟨S, H, hS, hH, -⟩ := h
    refine ⟨S, H, fun j hj => ?_, fun m hm => ?_⟩
    · rcases functionsIn_eq_subst_subset t₁ t₂ φ hj with h1 | h2
      · exact hS _ hmem_φ' h1
      · exact hS _ hmem_eq' h2
    · rcases functionsIn_eq_subst_subset t₁ t₂ φ hm with h1 | h2
      · exact hH _ hmem_φ' h1
      · exact hH _ hmem_eq' h2
  refine h.insert_entailed (φ.subst (fun _ => t₂)) hnew (fun σ hk hF => ?_)
  have heq := hF _ hmem_eq'
  have hφ1 := hF _ hmem_φ'
  rw [realizeWith_equal, termValueWith_relabel_inl, termValueWith_relabel_inl] at heq
  rw [realizeWith_subst_const] at hφ1 ⊢
  rw [← heq]
  exact hφ1

/-! ## Layer 6c: the maximal finite-support theory (Zorn)

The finite closure calculus (C0–C7) is turned into a complete theory over the finite-support
universe by a finite-character Zorn argument, mirroring `ConsistencyProperty.chain_closure`
but with completeness only for finite-support sentences — exactly what the restricted truth
lemma will need. Parameterized by a consistent seed (the base consistency hook is a separate
cross-file integration; the abstract machinery here fixes the shape it must feed). -/

/-- Negation on the finite-support universe. -/
def FSentence.not (τ : FSentence (L'' := L'') (J := J)) : FSentence (L'' := L'') (J := J) :=
  ⟨τ.1.not, τ.2.not⟩

variable (M)

open scoped Classical in
/-- **Finite-character Marker consistency** of a set of finite-support sentences: every finite
subset is Marker–Henkin consistent. This is the family Zorn runs over. -/
def MarkerConsistentFamily (X : Set (FSentence (L'' := L'') (J := J))) : Prop :=
  ∀ F : Finset (FSentence (L'' := L'') (J := J)), ↑F ⊆ X →
    MarkerHenkinConsistent M (F.image Subtype.val)

variable {M}

/-- Finite-character consistency is downward-closed in the set. -/
theorem MarkerConsistentFamily.mono {X X' : Set (FSentence (L'' := L'') (J := J))}
    (hXX : X' ⊆ X) (h : MarkerConsistentFamily M X) : MarkerConsistentFamily M X' :=
  fun F hF => h F (hF.trans hXX)

open scoped Classical in
/-- **Chain closure**: the union of a nonempty `⊆`-chain of finite-character-consistent sets is
finite-character consistent — a finite subset of the union lies in one chain member. -/
theorem MarkerConsistentFamily.sUnion_chain
    {𝒞 : Set (Set (FSentence (L'' := L'') (J := J)))}
    (h𝒞 : ∀ Y ∈ 𝒞, MarkerConsistentFamily M Y) (hchain : IsChain (· ⊆ ·) 𝒞)
    (hne : 𝒞.Nonempty) : MarkerConsistentFamily M (⋃₀ 𝒞) := by
  have key : ∀ F : Finset (FSentence (L'' := L'') (J := J)),
      (↑F : Set _) ⊆ ⋃₀ 𝒞 → ∃ Y ∈ 𝒞, (↑F : Set _) ⊆ Y := by
    intro F
    induction F using Finset.induction with
    | empty => intro _; obtain ⟨Y, hY⟩ := hne; exact ⟨Y, hY, by simp⟩
    | insert a s ha ih =>
      intro hsub
      have hsub' : (↑s : Set _) ⊆ ⋃₀ 𝒞 :=
        (Finset.coe_subset.mpr (Finset.subset_insert a s)).trans hsub
      obtain ⟨Y₁, hY₁, hsY₁⟩ := ih hsub'
      have haU : a ∈ ⋃₀ 𝒞 := hsub (by simp)
      obtain ⟨Y₂, hY₂, haY₂⟩ := haU
      rcases eq_or_ne Y₁ Y₂ with rfl | hne12
      · refine ⟨Y₁, hY₁, ?_⟩
        rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨haY₂, hsY₁⟩
      · rcases hchain.total hY₁ hY₂ with h12 | h21
        · refine ⟨Y₂, hY₂, ?_⟩
          rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨haY₂, hsY₁.trans h12⟩
        · refine ⟨Y₁, hY₁, ?_⟩
          rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨h21 haY₂, hsY₁⟩
  intro F hF
  obtain ⟨Y, hYmem, hFY⟩ := key F hF
  exact h𝒞 Y hYmem F hFY

open scoped Classical in
/-- **The maximal finite-support theory**: any finite-character-consistent seed extends to a
maximal one (Zorn, chain closure supplying the upper bounds). -/
theorem exists_maximal_markerConsistent (X₀ : Set (FSentence (L'' := L'') (J := J)))
    (hX₀ : MarkerConsistentFamily M X₀) :
    ∃ m, X₀ ⊆ m ∧ Maximal (MarkerConsistentFamily M) m := by
  refine zorn_subset_nonempty {X | MarkerConsistentFamily M X} (fun 𝒞 h𝒞S hchain hne => ?_)
    X₀ hX₀
  exact ⟨⋃₀ 𝒞, MarkerConsistentFamily.sUnion_chain (fun Y hY => h𝒞S hY) hchain hne,
    fun s hs => Set.subset_sUnion_of_mem hs⟩

/-! ### Membership calculus of the maximal theory -/

open scoped Classical in
/-- A sentence outside a maximal theory is refuted by some finite fragment: adjoining it to
that fragment breaks consistency. -/
theorem not_mem_of_maximal {m : Set (FSentence (L'' := L'') (J := J))}
    (hmax : Maximal (MarkerConsistentFamily M) m) {τ : FSentence (L'' := L'') (J := J)}
    (hτ : τ ∉ m) :
    ∃ F : Finset (FSentence (L'' := L'') (J := J)), ↑F ⊆ m ∧
      ¬ MarkerHenkinConsistent M (insert τ.val (F.image Subtype.val)) := by
  have h1 : ¬ MarkerConsistentFamily M (insert τ m) := fun hc =>
    hτ (hmax.2 hc (Set.subset_insert τ m) (Set.mem_insert τ m))
  simp only [MarkerConsistentFamily, not_forall] at h1
  obtain ⟨F, hFsub, hFncon⟩ := h1
  by_cases hτF : τ ∈ F
  · refine ⟨F.erase τ, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxτ, hxF⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hx)
      exact (Set.mem_insert_iff.mp (hFsub (Finset.mem_coe.mpr hxF))).resolve_left hxτ
    · have heq : F.image Subtype.val = insert τ.val ((F.erase τ).image Subtype.val) := by
        rw [← Finset.image_insert, Finset.insert_erase hτF]
      rw [heq] at hFncon; exact hFncon
  · exact absurd (hmax.1 F (fun x hx => (Set.mem_insert_iff.mp (hFsub hx)).resolve_left
      (fun heq => hτF (heq ▸ Finset.mem_coe.mp hx)))) hFncon

open scoped Classical in
/-- **Restricted completeness**: a maximal finite-support theory decides every finite-support
sentence. From maximality, `insert τ m` and `insert τ.not m` are both inconsistent as families
when `τ, τ.not ∉ m`; combining the two refuting fragments and applying the extension rule
yields a contradiction. -/
theorem MarkerConsistentFamily.mem_or_not_mem {m : Set (FSentence (L'' := L'') (J := J))}
    (hmax : Maximal (MarkerConsistentFamily M) m) (τ : FSentence (L'' := L'') (J := J)) :
    τ ∈ m ∨ FSentence.not τ ∈ m := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hτ, hτn⟩ := hcon
  obtain ⟨F₁, hF₁sub, hF₁ncon⟩ := not_mem_of_maximal hmax hτ
  obtain ⟨F₂, hF₂sub, hF₂ncon⟩ := not_mem_of_maximal hmax hτn
  have hGsub : (↑(F₁ ∪ F₂) : Set _) ⊆ m := by
    rw [Finset.coe_union]; exact Set.union_subset hF₁sub hF₂sub
  have hGcon : MarkerHenkinConsistent M ((F₁ ∪ F₂).image Subtype.val) := hmax.1 _ hGsub
  have h₁ : (F₁.image Subtype.val) ⊆ (F₁ ∪ F₂).image Subtype.val :=
    Finset.image_subset_image Finset.subset_union_left
  have h₂ : (F₂.image Subtype.val) ⊆ (F₁ ∪ F₂).image Subtype.val :=
    Finset.image_subset_image Finset.subset_union_right
  rcases hGcon.extension τ.val τ.2 with hc | hc
  · exact hF₁ncon (hc.mono (Finset.insert_subset_insert _ h₁))
  · exact hF₂ncon (hc.mono (Finset.insert_subset_insert _ h₂))

open scoped Classical in
/-- **The membership-insertion principle** for the maximal theory: a finite-support sentence
whose adjunction to every fragment of `m` stays consistent is a member of `m`. This turns each
fragment-level closure rule into a membership rule. -/
theorem MarkerConsistentFamily.mem_of_insert_consistent
    {m : Set (FSentence (L'' := L'') (J := J))}
    (hmax : Maximal (MarkerConsistentFamily M) m) (new : FSentence (L'' := L'') (J := J))
    (hins : ∀ F : Finset (FSentence (L'' := L'') (J := J)), ↑F ⊆ m →
      MarkerHenkinConsistent M (insert new.val (F.image Subtype.val))) : new ∈ m := by
  have hcons : MarkerConsistentFamily M (insert new m) := by
    intro F hF
    by_cases hnew : new ∈ F
    · have heq : F.image Subtype.val = insert new.val ((F.erase new).image Subtype.val) := by
        rw [← Finset.image_insert, Finset.insert_erase hnew]
      rw [heq]
      refine hins (F.erase new) (fun x hx => ?_)
      obtain ⟨hxnew, hxF⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hx)
      exact (Set.mem_insert_iff.mp (hF (Finset.mem_coe.mpr hxF))).resolve_left hxnew
    · exact hmax.1 F (fun x hx => (Set.mem_insert_iff.mp (hF hx)).resolve_left
        (fun heq => hnew (heq ▸ Finset.mem_coe.mp hx)))
  exact hmax.2 hcons (Set.subset_insert new m) (Set.mem_insert new m)

open scoped Classical in
/-- **The membership-closure engine**: a fragment-level closure rule (adjoining `new` to any
consistent fragment containing the trigger stays consistent) lifts, given `trigger ∈ m`, to
`new ∈ m`. Every named closure membership rule below is a one-line instance. -/
theorem MarkerConsistentFamily.mem_of_trigger {m : Set (FSentence (L'' := L'') (J := J))}
    (hmax : Maximal (MarkerConsistentFamily M) m) {trigger : FSentence (L'' := L'') (J := J)}
    (htrig : trigger ∈ m) (new : FSentence (L'' := L'') (J := J))
    (rule : ∀ (G : Finset ((L''[[J]])[[ℕ]].Sentenceω)), trigger.val ∈ G →
      MarkerHenkinConsistent M G → MarkerHenkinConsistent M (insert new.val G)) : new ∈ m := by
  refine MarkerConsistentFamily.mem_of_insert_consistent hmax new (fun F hF => ?_)
  have hsub : (↑(insert trigger F) : Set _) ⊆ m := by
    rw [Finset.coe_insert]; exact Set.insert_subset_iff.mpr ⟨htrig, hF⟩
  have hGcon : MarkerHenkinConsistent M ((insert trigger F).image Subtype.val) := hmax.1 _ hsub
  rw [Finset.image_insert] at hGcon
  exact (rule _ (Finset.mem_insert_self trigger.val (F.image Subtype.val)) hGcon).mono
    (Finset.insert_subset_insert _ (Finset.subset_insert _ _))

/-- **`C2` in membership form**: `¬¬φ ∈ m` implies `φ ∈ m`. -/
theorem MarkerConsistentFamily.mem_not_not {m : Set (FSentence (L'' := L'') (J := J))}
    (hmax : Maximal (MarkerConsistentFamily M) m) {φ : FSentence (L'' := L'') (J := J)}
    (hmem : FSentence.not (FSentence.not φ) ∈ m) : φ ∈ m :=
  MarkerConsistentFamily.mem_of_trigger hmax hmem φ (fun _ htg hG => hG.not_not htg)

end FiniteClosure

end FirstOrder.Language
