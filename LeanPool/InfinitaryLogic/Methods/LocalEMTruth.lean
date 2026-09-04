/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMContext
/-!
# The local EM truth lemma, layer 1: truth kernel + Skolem-witness transport

This file assembles the pieces the restricted local truth lemma consumes, in two parts.

**The generic truth kernel** (`section TruthKernel`, over any `[Λ.Structure M]`): the eventual-deep-
truth predicate `LocalEMContext.eventualDeepTruth`, the carrier substitution bridge
`realize_term_mkClass`, the atom cases `eventualDeepTruth_equal_iff`/`_rel_iff`, the 0-1 decidedness
law `eventualDeepTruth_decided`, the `imp`/`falsum` connective cases
(`eventually_imp_iff_imp_eventually`,
`eventualDeepTruth_falsum_iff`, `eventualDeepTruth_imp_iff`), and the `all`-case class/snoc bridge
`mkClass_snoc`. Ported from `EMTermModel.lean:820–1115`. These are generic over `Λ` (they touch only
the generic quotient structure + realize bridges), so no `localColim`-specific plumbing is needed.

**The Skolem-witness transport** (`section WitnessTransport`, over `localColim s₀`): the restricted
truth lemma's `all` case (`∀ψ`) needs, in the source model, the Hilbert-choice witness of `¬ψ` as an
actual closed term of `(localColim s₀)[[J]]`, together with the semantic "witness universality" it
delivers. This part builds exactly that transport, mirroring the
`skWitnessTerm`/`deepInterp_skWitness`/`skWitness_universal` chain of `EMTermModel.lean` but
over the
**countable** local tower:

* `locSkWitnessTerm` — the colimit-level witness term for a stage-`k` universal `∀ψ ∈ Γlocal s₀ k`,
  built from the local Skolem symbol `skolemNeedSymbol h` (witnessing `∃ xₙ, ¬ψ`), included through
  `LlocalInclusion s₀ (k+1)` and then `lhomWithConstants`;
* `locJSupport_locSkWitnessTerm` — its head is an `L`-function symbol, not a `J`-constant, so its
  `J`-support is just the union of the arguments';
* `locDeepInterp_skWitness` — its deep interpretation is exactly the Hilbert-choice value for `¬ψ`
  on the deep interpretations of the arguments (the `localColimStructure`/`localStageStructure`/
  `localSkolemStructure` funMap coherence is fully definitional, so this is `rfl` after unfolding);
* `locSkWitness_universal` — the Skolem-axiom transport: if `ψ` holds at the deep tuple extended by
  the witness's deep value, then it holds at *every* `M`-element. Powered by
  `localSkolem_funMap_spec`
  (in `LocalSkolem.lean`) and the realization transport `realize_map_LlocalInclusion`.

This is the local analogue of `EMTermModel.lean:114–180`. It is a pure file (imports
`LocalEMContext`, not the Conditional-touching `LocalEMExtraction`) so the local context/truth stack
stays off the EM stack.
-/

namespace FirstOrder.Language

/-! ## The generic truth kernel

The atom/connective rewrite API and the eventual-deep-truth decidedness fact, generic over any
`[Λ.Structure M]` (they only touch the generic quotient structure of `LocalEMContext.lean` plus the
`realize_locDeForm`/`locDeepInterp_onTerm_subst` bridges — no `localColim`-specific plumbing). The
`OmegaComplete` mixin, `TLReady`, and the staged induction are later layers. -/

section TruthKernel

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J] {M : Type} [Λ.Structure M]

/-- **Eventual deep truth** of a base-language formula `φ` on a tuple of closed argument
terms over a
support `S`: `φ` holds in `M` on the deep interpretations of the terms, for all sufficiently
deep `d`.
The right-hand side of the restricted truth lemma. Local analogue of
  `EMContext.eventualDeepTruth`. -/
def LocalEMContext.eventualDeepTruth (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (φ : Λ.BoundedFormulaω Empty n) (ts : Fin n → Λ[[J]].Term Empty) (S : Finset J) : Prop :=
  ∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => locDeepInterp Λ J ctx.a d S (ts i)

/-- **Carrier-side term substitution**: realizing a term in the local EM term model under the
assignment `Sum.elim Empty.elim (mkClass ∘ ts)` gives the class of the substituted closed term. By
induction on the term, using `funMap_mkClass`. Local analogue of
  `EMContext.realize_term_mkClass`. -/
private theorem LocalEMContext.realize_term_mkClass (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (ts : Fin n → Λ[[J]].Term Empty)
    (t : Λ[[J]].Term (Empty ⊕ Fin n)) :
    @Term.realize (Λ[[J]]) ctx.Carrier ctx.structure (Empty ⊕ Fin n)
        (Sum.elim Empty.elim fun i => ctx.mkClass (t := ts i)) t
      = ctx.mkClass (t := t.subst (Sum.elim (fun e => e.elim) ts)) := by
  induction t with
  | var x => cases x with
    | inl e => exact e.elim
    | inr i => rfl
  | func f args ih =>
    have hargs : (fun j => @Term.realize (Λ[[J]]) ctx.Carrier ctx.structure _
          (Sum.elim Empty.elim fun i => ctx.mkClass (t := ts i)) (args j))
        = (fun j => ctx.mkClass (t := (args j).subst (Sum.elim (fun e => e.elim) ts))) := funext ih
    change @Structure.funMap (Λ[[J]]) ctx.Carrier ctx.structure _ f _ = _
    rw [hargs, ctx.funMap_mkClass]
    rfl

/-- **Truth lemma, equality-atom case**: realizing a base-language equality atom in the
local EM term
model on a tuple of term-classes is equivalent to its eventual deep truth. Carrier side via
`realize_term_mkClass`; quotient side via `Quotient.eq`; deep side via
`eventually_locDeepInterp_superset_iff` and `locDeepInterp_onTerm_subst`. -/
theorem LocalEMContext.eventualDeepTruth_equal_iff (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (t₁ t₂ : Λ.Term (Empty ⊕ Fin n))
    (ts : Fin n → Λ[[J]].Term Empty) {S : Finset J}
    (hS : locJSupport Λ J (((lhomWithConstants Λ J).onTerm t₁).subst
            (Sum.elim (fun e => e.elim) ts))
          ∪ locJSupport Λ J (((lhomWithConstants Λ J).onTerm t₂).subst
            (Sum.elim (fun e => e.elim) ts)) ⊆ S) :
    @BoundedFormulaω.Realize (Λ[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.equal t₁ t₂).mapLanguage (lhomWithConstants Λ J))
        Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
      LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (BoundedFormulaω.equal t₁ t₂)
        ts S := by
  have hcarrier : @BoundedFormulaω.Realize (Λ[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.equal t₁ t₂).mapLanguage (lhomWithConstants Λ J))
        Empty.elim (fun i => ctx.mkClass (t := ts i))
      ↔ ctx.mkClass (t := ((lhomWithConstants Λ J).onTerm t₁).subst
            (Sum.elim (fun e => e.elim) ts))
        = ctx.mkClass (t := ((lhomWithConstants Λ J).onTerm t₂).subst
            (Sum.elim (fun e => e.elim) ts)) := by
    let : Λ[[J]].Structure ctx.Carrier := ctx.structure
    rw [show (BoundedFormulaω.equal t₁ t₂).mapLanguage (lhomWithConstants Λ J)
        = BoundedFormulaω.equal ((lhomWithConstants Λ J).onTerm t₁)
            ((lhomWithConstants Λ J).onTerm t₂) from rfl,
      BoundedFormulaω.realize_equal, LocalEMContext.realize_term_mkClass (Λ := Λ) (J := J) ctx ts,
      LocalEMContext.realize_term_mkClass (Λ := Λ) (J := J) ctx ts]
  have hcommon : LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx
        (BoundedFormulaω.equal t₁ t₂) ts S ↔
      (∀ᶠ d in Filter.atTop,
        locDeepInterp Λ J ctx.a d S (((lhomWithConstants Λ J).onTerm t₁).subst
            (Sum.elim (fun e => e.elim) ts))
          = locDeepInterp Λ J ctx.a d S (((lhomWithConstants Λ J).onTerm t₂).subst
            (Sum.elim (fun e => e.elim) ts))) := by
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun d => ?_)
    rw [BoundedFormulaω.realize_equal, ← locDeepInterp_onTerm_subst, ← locDeepInterp_onTerm_subst]
  rw [hcarrier, hcommon]
  change Quotient.mk ctx.setoid _ = Quotient.mk ctx.setoid _ ↔ _
  rw [Quotient.eq]
  change LocalEMEq Λ J ctx.a _ _ ↔ _
  unfold LocalEMEq
  exact Filter.eventually_congr (eventually_locDeepInterp_superset_iff Λ J ctx.a ctx.hind
    (ctx.atom_mem _ _ _ Finset.subset_union_left Finset.subset_union_right) hS)

/-- **Truth lemma, relation-atom case**: realizing a base-language relation atom in the
local EM term
model on a tuple of term-classes is equivalent to its eventual deep truth. Carrier side via
`realize_term_mkClass`; then `relMap_mkClass_iff`; deep side via `locDeepInterp_onTerm_subst`. -/
theorem LocalEMContext.eventualDeepTruth_rel_iff (ctx : LocalEMContext Λ J (M := M)) {n l : ℕ}
    (R : Λ.Relations l) (args : Fin l → Λ.Term (Empty ⊕ Fin n))
    (ts : Fin n → Λ[[J]].Term Empty) {S : Finset J}
    (hS : (Finset.univ.biUnion fun i => locJSupport Λ J
            (((lhomWithConstants Λ J).onTerm (args i)).subst
              (Sum.elim (fun e => e.elim) ts))) ⊆ S) :
    @BoundedFormulaω.Realize (Λ[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.rel R args).mapLanguage (lhomWithConstants Λ J))
        Empty.elim (fun i => ctx.mkClass (t := ts i)) ↔
      LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (BoundedFormulaω.rel R args) ts S := by
  have hcarrier : @BoundedFormulaω.Realize (Λ[[J]]) ctx.Carrier ctx.structure Empty n
        ((BoundedFormulaω.rel R args).mapLanguage (lhomWithConstants Λ J))
        Empty.elim (fun i => ctx.mkClass (t := ts i))
      ↔ @Structure.RelMap (Λ[[J]]) ctx.Carrier ctx.structure l (Sum.inl R)
          (fun i => ctx.mkClass (t := ((lhomWithConstants Λ J).onTerm (args i)).subst
            (Sum.elim (fun e => e.elim) ts))) := by
    let : Λ[[J]].Structure ctx.Carrier := ctx.structure
    rw [show (BoundedFormulaω.rel R args).mapLanguage (lhomWithConstants Λ J)
        = BoundedFormulaω.rel (Sum.inl R)
            (fun i => (lhomWithConstants Λ J).onTerm (args i)) from rfl]
    refine Iff.of_eq (congrArg
      (@Structure.RelMap (Λ[[J]]) ctx.Carrier ctx.structure l (Sum.inl R)) ?_)
    funext i
    exact LocalEMContext.realize_term_mkClass (Λ := Λ) (J := J) ctx ts _
  have hcommon : LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx
        (BoundedFormulaω.rel R args) ts S ↔
      (∀ᶠ d in Filter.atTop,
        Structure.RelMap R fun i => locDeepInterp Λ J ctx.a d S
          (((lhomWithConstants Λ J).onTerm (args i)).subst
            (Sum.elim (fun e => e.elim) ts))) := by
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun d => ?_)
    rw [BoundedFormulaω.realize_rel]
    apply Iff.of_eq
    congr 1
    funext i
    exact (locDeepInterp_onTerm_subst Λ J ctx.a d S (args i) ts).symm
  rw [hcarrier, hcommon]
  exact LocalEMContext.relMap_mkClass_iff (Λ := Λ) (J := J) ctx R
    (fun i => ((lhomWithConstants Λ J).onTerm (args i)).subst
      (Sum.elim (fun e => e.elim) ts)) hS

/-- **0-1 law for eventual deep truth** (the unlock for the truth lemma's `imp`/connective
cases): if
the de-substituted formula `locDeForm S φ ts` lies in the tail-indiscernible family `Γ`, then `φ`'s
eventual deep truth is *decided*. The value is eventually constant because tail
indiscernibility makes
all sufficiently-deep consecutive tuples agree on the single arity-`S.card` formula. Local
analogue of
`EMContext.eventualDeepTruth_decided`. -/
theorem LocalEMContext.eventualDeepTruth_decided (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (φ : Λ.BoundedFormulaω Empty n)
    (ts : Fin n → Λ[[J]].Term Empty) (S : Finset J)
    (hsub : ∀ i, locJSupport Λ J (ts i) ⊆ S)
    (hmem : (⟨S.card, locDeForm Λ J S φ ts hsub⟩ :
        Σ n, Λ.BoundedFormulaω Empty n) ∈ ctx.Γ) :
    (∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => locDeepInterp Λ J ctx.a d S (ts i)) ∨
      (∀ᶠ d in Filter.atTop, ¬ φ.Realize Empty.elim fun i => locDeepInterp Λ J ctx.a d S (ts
        i)) := by
  obtain ⟨N, hN⟩ := ctx.hind hmem
  have hmono : ∀ d : ℕ, StrictMono (fun i : Fin S.card => d + (i : ℕ)) :=
    fun d _ _ hii' => Nat.add_lt_add_left hii' d
  by_cases hbase :
      (locDeForm Λ J S φ ts hsub).Realize Empty.elim (fun i : Fin S.card => ctx.a (N + (i : ℕ)))
  · refine Or.inl (Filter.eventually_atTop.mpr ⟨N, fun d hd => ?_⟩)
    rw [← realize_locDeForm Λ J ctx.a d S φ ts hsub]
    exact (hN (fun i => d + (i : ℕ)) (fun i => N + (i : ℕ)) (hmono d) (hmono N)
      (fun k => le_trans hd (Nat.le_add_right d k)) (fun k => Nat.le_add_right N k)).mpr hbase
  · refine Or.inr (Filter.eventually_atTop.mpr ⟨N, fun d hd hPd => hbase ?_⟩)
    rw [← realize_locDeForm Λ J ctx.a d S φ ts hsub] at hPd
    exact (hN (fun i => N + (i : ℕ)) (fun i => d + (i : ℕ)) (hmono N) (hmono d)
      (fun k => Nat.le_add_right N k) (fun k => le_trans hd (Nat.le_add_right d k))).mpr hPd

/-- An eventual implication splits as an implication of eventuals exactly when the antecedent's
eventual truth is *decided*. The Filter fact behind the truth lemma's `imp` case — only the
antecedent's decidedness is needed. -/
private theorem eventually_imp_iff_imp_eventually {α : Type*} {f : Filter α} {P Q : α → Prop}
    (hP : (∀ᶠ x in f, P x) ∨ (∀ᶠ x in f, ¬ P x)) :
    (∀ᶠ x in f, P x → Q x) ↔ ((∀ᶠ x in f, P x) → (∀ᶠ x in f, Q x)) := by
  constructor
  · intro h hP'
    exact (h.and hP').mono fun _ p => p.1 p.2
  · intro h
    rcases hP with hP | hP
    · exact (h hP).mono fun _ hQ _ => hQ
    · exact hP.mono fun _ hnp hp => absurd hp hnp

/-- **Truth lemma, falsum case** (eventual-deep-truth side): `falsum` has no eventual deep truth.
Immediate from `Filter.eventually_const` (`atTop` on `ℕ` is `NeBot`). -/
theorem LocalEMContext.eventualDeepTruth_falsum_iff (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (ts : Fin n → Λ[[J]].Term Empty) (S : Finset J) :
    LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (BoundedFormulaω.falsum) ts S ↔
      False := by
  simp only [LocalEMContext.eventualDeepTruth, BoundedFormulaω.realize_falsum]
  exact Filter.eventually_const

/-- **Truth lemma, imp case** (eventual-deep-truth side): the eventual deep truth of `φ ⟹ ψ` is the
implication of their eventual deep truths, *provided* `φ`'s eventual deep truth is decided
(supplied by
`eventualDeepTruth_decided`). Local analogue of `EMContext.eventualDeepTruth_imp_iff`. -/
theorem LocalEMContext.eventualDeepTruth_imp_iff (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (φ ψ : Λ.BoundedFormulaω Empty n)
    (ts : Fin n → Λ[[J]].Term Empty) (S : Finset J)
    (hdec :
      (∀ᶠ d in Filter.atTop, φ.Realize Empty.elim fun i => locDeepInterp Λ J ctx.a d S (ts i)) ∨
        (∀ᶠ d in Filter.atTop, ¬ φ.Realize Empty.elim
          fun i => locDeepInterp Λ J ctx.a d S (ts i))) :
    LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx (φ.imp ψ) ts S ↔
      (LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx φ ts S →
        LocalEMContext.eventualDeepTruth (Λ := Λ) (J := J) ctx ψ ts S) := by
  simp only [LocalEMContext.eventualDeepTruth, BoundedFormulaω.realize_imp]
  exact eventually_imp_iff_imp_eventually hdec

/-- Forming classes commutes with `Fin.snoc`: the carrier tuple obtained by snocing `mkClass u` onto
`mkClass ∘ ts` is `mkClass ∘ (Fin.snoc ts u)`. The bridge between the carrier-side `∀x` (over
term-classes) and the term-side `Fin.snoc ts u` in the `all` case. Local analogue of
`EMContext.mkClass_snoc`. -/
theorem LocalEMContext.mkClass_snoc (ctx : LocalEMContext Λ J (M := M)) {m : ℕ}
    (ts : Fin m → Λ[[J]].Term Empty) (u : Λ[[J]].Term Empty) :
    Fin.snoc (fun i => ctx.mkClass (t := ts i)) (ctx.mkClass (t := u))
      = fun i => ctx.mkClass
          (t := (Fin.snoc ts u : Fin (m + 1) → Λ[[J]].Term Empty) i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

end TruthKernel

/-! ## Local Skolem-witness transport (over `localColim s₀`) -/

section WitnessTransport

variable (s₀ : LocalStage) (J : Type) [LinearOrder J]

/-- The **colimit-level local Skolem-witness term** for a stage-`k` universal `∀ψ ∈ Γlocal s₀ k`:
the local Skolem symbol `skolemNeedSymbol h` (witnessing `∃ xₙ, ¬ψ`), in the `localSkolem`
summand of
`Llocal s₀ (k+1)`, included through `LlocalInclusion s₀ (k+1)` and then `lhomWithConstants`, applied
to the closed argument terms `ts`. Local analogue of `skWitnessTerm`. -/
def locSkWitnessTerm {k n : ℕ} {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) : (localColim s₀)[[J]].Term Empty :=
  Term.func ((lhomWithConstants (localColim s₀) J).onFunction
    ((LlocalInclusion s₀ (k + 1)).onFunction
      (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n))) ts

/-- The witness term mentions only the `J`-constants of its arguments (its head is an
`L`-function symbol, not a skeleton constant), so its support is covered whenever the arguments' is.
Local analogue of `jSupport_skWitnessTerm`. -/
theorem locJSupport_locSkWitnessTerm {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) :
    locJSupport (localColim s₀) J (locSkWitnessTerm s₀ J h ts)
      = Finset.univ.biUnion fun i => locJSupport (localColim s₀) J (ts i) := by
  have hjc : locJConstOf (localColim s₀) J ((lhomWithConstants (localColim s₀) J).onFunction
      ((LlocalInclusion s₀ (k + 1)).onFunction (Sum.inr (skolemNeedSymbol h)))) = ∅ := by
    cases n <;> rfl
  rw [locSkWitnessTerm,
    show locJSupport (localColim s₀) J
        (Term.func ((lhomWithConstants (localColim s₀) J).onFunction
          ((LlocalInclusion s₀ (k + 1)).onFunction (Sum.inr (skolemNeedSymbol h)))) ts)
      = (Finset.univ.biUnion fun i => locJSupport (localColim s₀) J (ts i))
        ∪ locJConstOf (localColim s₀) J ((lhomWithConstants (localColim s₀) J).onFunction
            ((LlocalInclusion s₀ (k + 1)).onFunction (Sum.inr (skolemNeedSymbol h)))) from rfl,
    hjc, Finset.union_empty]

section Semantic

variable {M : Type} [s₀.Lang.Structure M] [Nonempty M] (a : ℕ → M)

end Semantic

end WitnessTransport

end FirstOrder.Language
