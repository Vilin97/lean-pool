/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The many-sorted proof system, and the non-derivability half of Proposition 30.
arXiv:2608.13306v1, Section 8.

  "Say that a sort s FEEDS a sort t if s = t or some symbol has an argument of
   sort s and result sort t. Write s ⇒ t for the reflexive transitive closure.
   In this signature no symbol has an argument of sort a, so a ⇒ t holds only
   for t = a.

   Every rule of Figure 2 has premises whose sorts feed the sort of its
   conclusion. Modus ponens and the quantifier rules are sort-preserving, and
   framing puts a pattern of sort s into one argument position of a symbol, so
   its conclusion has that symbol's result sort t, and such a symbol has an
   argument of sort s. So if the conclusion of a rule has sort t ≠ a, then no
   premise of it has sort a.

   By induction on derivations, every line whose sort is not a is derivable from
   the axioms alone. A hypothesis line has sort a and is excluded, an axiom line
   needs nothing, and a rule with conclusion of sort t ≠ a has, by the previous
   paragraph, no premise of sort a. The induction hypothesis therefore applies to
   all of its premises. Since φ has sort c, from Γ ⊢ φ we would get ⊢ φ and hence
   ⊨ φ by (S). But φ is not valid."

DESIGN RULINGS:

* The many-sorted Figure 2 is written out in full rather than abstracted behind
  a "sort-feeding" hypothesis. The paper's argument is that Figure 2 HAS that
  property; assuming it instead would prove a weaker and much less interesting
  statement.
* Many-sorted soundness is a HYPOTHESIS, as in the paper, which cites it to
  [3, Thm. 13] rather than proving it: "Soundness is the implication from Γ⊢φ to
  Γ⊨φ and is proved in [3, Thm. 13]. Input (S) of Section 2 is its one-sorted
  case." Our one-sorted `soundness` is proved; this is its many-sorted analogue
  and is not.
* Γ is taken homogeneous at one sort. Proposition 30's Γ is a singleton of
  sort `a`, and the induction below is stated in terms of that sort.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.Sorted
import LeanPool.MatchingLogic.ProofSystem  -- for PForm and PForm.Taut
import LeanPool.MatchingLogic.EntryPoints

/-!
# MatchingLogic.SortedProof
-/

-- `PForm` lives in ProofSystem.lean. Without this import, `autoImplicit` turns
-- every mention of it into a fresh type VARIABLE and the file still elaborates
-- most of the way, failing later with an unrelated-looking pattern-match error.
namespace MatchingLogic
namespace Sorted

variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]

/-! ### Free variables, at a sort -/

/-- The free variables of a many-sorted pattern, paired with the sort at which
they occur. -/
def MFV : {s : S.Srt} → MPattern S Var s → Set (S.Srt × Var)
  | _, .var x s => {(s, x)}
  | _, .bot => ∅
  | _, .app _ f => ⋃ i, MFV (f i)
  | _, .imp a b => MFV a ∪ MFV b
  | _, .ex x s' a => MFV a \ {(s', x)}

/-! ### Application contexts, at sorts -/

/-- `C ::= □ | σ(φ₁, …, C, …, φₙ)`, tracking both the hole's sort and the
context's result sort. -/
inductive MAppCtx (S : MSignature) (Var : Type) : S.Srt → S.Srt → Type where
  | hole : {s : S.Srt} → MAppCtx S Var s s
  | node : {sh : S.Srt} → (σ : S.Sym) → (i : Fin (S.arity σ)) →
      ((j : Fin (S.arity σ)) → MPattern S Var (S.argSort σ j)) →
      MAppCtx S Var sh (S.argSort σ i) → MAppCtx S Var sh (S.resSort σ)

/-- `C[φ]`. -/
def MAppCtx.plug : {sh st : S.Srt} → MAppCtx S Var sh st → MPattern S Var sh →
    MPattern S Var st
  | _, _, .hole, φ => φ
  | _, _, .node σ i args c, φ => .app σ (Function.update args i (c.plug φ))

/-! ### Variable-for-variable substitution, at a sort -/

/-- `φ[y/x]` where `x` and `y` are variables of sort `s'`.  As in the one-sorted
development, substitution is variable-for-variable only and capture-avoidance is
a side condition rather than a renaming. -/
def msubstVar (s' : S.Srt) (x y : Var) :
    {s : S.Srt} → MPattern S Var s → MPattern S Var s
  | _, .var z t => if t = s' ∧ z = x then .var y t else .var z t
  | _, .bot => .bot
  | _, .app σ f => .app σ (fun i => msubstVar s' x y (f i))
  | _, .imp a b => .imp (msubstVar s' x y a) (msubstVar s' x y b)
  | _, .ex z t a =>
      if t = s' ∧ z = x then .ex z t a else .ex z t (msubstVar s' x y a)

/-- Capture-avoidance for `msubstVar`, with the same three alternatives as the
one-sorted `CaptureFree`: the substitution stops here, or it changes nothing
here, or this binder cannot capture `y`.  The middle alternative is the one an
audit had to restore in the one-sorted case. -/
def MCaptureFree (s' : S.Srt) (x y : Var) :
    {s : S.Srt} → MPattern S Var s → Prop
  | _, .var _ _ => True
  | _, .bot => True
  | _, .app _ f => ∀ i, MCaptureFree s' x y (f i)
  | _, .imp a b => MCaptureFree s' x y a ∧ MCaptureFree s' x y b
  | _, .ex z t a =>
      (t = s' ∧ z = x) ∨ (s', x) ∉ MFV a ∨
        (¬ (t = s' ∧ z = y) ∧ MCaptureFree s' x y a)

/-! ### Figure 2, many-sorted -/

/-- Propositional tautology instances, at a sort. -/
def substPF {s : S.Srt} (θ : Nat → MPattern S Var s) :
    PForm → MPattern S Var s
  | PForm.atom n => θ n
  | PForm.bot => MPattern.bot
  | PForm.imp a b => MPattern.imp (substPF θ a) (substPF θ b)

/-- `Γ ⊢ φ` for a many-sorted theory `Γ`, all of whose members have sort `sΓ`.
The rules are those of Figure 2, taken "at each symbol and each argument
position", with the premise at the sort of that position and the conclusion at
the symbol's result sort. -/
inductive MProvable {sΓ : S.Srt} (Γ : Set (MPattern S Var sΓ)) :
    {s : S.Srt} → MPattern S Var s → Prop
  | hyp {φ} : φ ∈ Γ → MProvable Γ φ
  | taut {s : S.Srt} {p : PForm} {θ : Nat → MPattern S Var s} :
      PForm.Taut p → MProvable Γ (substPF θ p)
  | mp {s : S.Srt} {φ₁ φ₂ : MPattern S Var s} :
      MProvable Γ φ₁ → MProvable Γ (.imp φ₁ φ₂) → MProvable Γ φ₂
  | exQuant {s s' : S.Srt} {x y : Var} {φ : MPattern S Var s} :
      MCaptureFree s' x y φ →
      MProvable Γ (.imp (msubstVar s' x y φ) (.ex x s' φ))
  | exGen {s s' : S.Srt} {x : Var} {φ₁ φ₂ : MPattern S Var s} :
      MProvable Γ (.imp φ₁ φ₂) → (s', x) ∉ MFV φ₂ →
      MProvable Γ (.imp (.ex x s' φ₁) φ₂)
  | propBot {σ : S.Sym} {i : Fin (S.arity σ)} {args} :
      MProvable Γ (.imp (.app σ (Function.update args i .bot)) .bot)
  | propOr {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      MProvable Γ (.imp (.app σ (Function.update args i (MPattern.orP φ₁ φ₂)))
        (MPattern.orP (.app σ (Function.update args i φ₁))
                      (.app σ (Function.update args i φ₂))))
  | propEx {σ : S.Sym} {i : Fin (S.arity σ)} {args} {s' : S.Srt} {x : Var} {φ} :
      (∀ j, j ≠ i → (s', x) ∉ MFV (args j)) →
      MProvable Γ (.imp (.app σ (Function.update args i (.ex x s' φ)))
        (.ex x s' (.app σ (Function.update args i φ))))
  | framing {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      MProvable Γ (.imp φ₁ φ₂) →
      MProvable Γ (.imp (.app σ (Function.update args i φ₁))
                        (.app σ (Function.update args i φ₂)))
  | existence {s : S.Srt} {x : Var} :
      MProvable Γ (.ex x s (.var x s))
  | singleton {sh st : S.Srt} {x : Var} {φ : MPattern S Var sh}
      (C₁ C₂ : MAppCtx S Var sh st) :
      MProvable Γ (.imp (C₁.plug (MPattern.and (.var x sh) φ))
        (MPattern.nt (C₂.plug (MPattern.and (.var x sh) (MPattern.nt φ)))))

/-! ### Sort feeding -/

/-- `s` feeds `t`: `s = t`, or some symbol has an argument of sort `s` and
result sort `t` (paper, Section 8). -/
def Feeds (S : MSignature) (s t : S.Srt) : Prop :=
  s = t ∨ ∃ (σ : S.Sym) (i : Fin (S.arity σ)), S.argSort σ i = s ∧ S.resSort σ = t

/-- `⇒`, the reflexive transitive closure of `Feeds`. -/
abbrev FeedsStar (S : MSignature) : S.Srt → S.Srt → Prop :=
  Relation.ReflTransGen (Feeds S)

/-- **In `S3`, sort `a` feeds only itself**, because no symbol has an argument
of sort `a`.  This is the structural fact the whole argument rests on. -/
theorem feedsStar_a_only_a (t : Srt3) : FeedsStar S3 Srt3.a t → t = Srt3.a := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hfeed ih =>
      rcases hfeed with hsame | ⟨σ, i, harg, _⟩
      · exact hsame ▸ ih
      · rw [ih] at harg
        cases σ <;> cases harg

/-! ### Many-sorted soundness, assumed as the paper does -/

/-- `(S)` at many sorts.  The paper cites this to [3, Thm. 13] rather than
proving it; our one-sorted `soundness` is proved, this is not.

NARROWER THAN THE PAPER, deliberately: this quantifies only over HOMOGENEOUS
theories, whereas the paper's many-sorted theories may mix sorts. That is
exactly sufficient for Proposition 30, whose `Γ` is a singleton at sort `a`, and
it keeps the induction below stated in terms of a single `sΓ`. An audit flagged
the narrowing, so it is recorded here rather than silent. -/
def MSoundness (S : MSignature) (Var : Type) [DecidableEq S.Srt] [DecidableEq Var] : Prop :=
  ∀ {sΓ sφ : S.Srt} (Γ : Set (MPattern S Var sΓ)) (φ : MPattern S Var sφ),
    MProvable Γ φ → MGlobalCons Γ φ

/-! ### Proposition 30, third claim -/

/-- Every line of a derivation whose sort does not feed back to `sΓ` is
derivable from the axioms alone: a hypothesis line has sort `sΓ`, and no rule
carries an `sΓ` premise into a conclusion of a sort that `sΓ` does not feed. -/
theorem mprovable_empty_of_not_feeds {sΓ s : S.Srt}
    (Γ : Set (MPattern S Var sΓ)) (φ : MPattern S Var s)
    (hfeed : ¬ FeedsStar S sΓ s) (h : MProvable Γ φ) :
    MProvable (∅ : Set (MPattern S Var sΓ)) φ := by
  revert hfeed
  induction h with
  | hyp hφ =>
      intro hfeed
      exact (hfeed Relation.ReflTransGen.refl).elim
  | taut hp =>
      intro _
      exact .taut hp
  | mp _ _ ih₁ ih₂ =>
      intro hfeed
      exact .mp (ih₁ hfeed) (ih₂ hfeed)
  | exQuant hfree =>
      intro _
      exact .exQuant hfree
  | exGen _ hfree ih =>
      intro hfeed
      exact .exGen (ih hfeed) hfree
  | propBot =>
      intro _
      exact .propBot
  | propOr =>
      intro _
      exact .propOr
  | propEx hfree =>
      intro _
      exact .propEx hfree
  | @framing σ i args φ₁ φ₂ _ ih =>
      intro hfeed
      apply MProvable.framing
      apply ih
      intro hpath
      apply hfeed
      exact hpath.tail (Or.inr ⟨σ, i, rfl, rfl⟩)
  | existence =>
      intro _
      exact .existence
  | singleton C₁ C₂ =>
      intro _
      exact .singleton C₁ C₂

/-- **Proposition 30, third claim.**  `Γ ⊬ φ`.

`φ` has sort `c`, and `a` feeds only `a`, so any derivation of `φ` from `Γ`
would be a derivation from no hypotheses; soundness would then make `φ` valid,
and it is not — take `M_b = {r, s}` with `g_M(r) ≠ g_M(s)`. -/
theorem Γ3_not_derives_φ3 (hS : MSoundness S3 Var) (x y : Var) (hxy : x ≠ y) :
    ¬ MProvable (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) := by
  intro hprov
  have hnotfeed : ¬ FeedsStar S3 Srt3.a Srt3.c := by
    intro hfeed
    have hac := feedsStar_a_only_a Srt3.c hfeed
    cases hac
  have hempty : MProvable (∅ : Set (MPattern S3 Var Srt3.a))
      (φ3 (Var := Var) x y) :=
    mprovable_empty_of_not_feeds _ _ hnotfeed hprov
  have hvalid : MGlobalCons (∅ : Set (MPattern S3 Var Srt3.a))
      (φ3 (Var := Var) x y) :=
    hS _ _ hempty
  let M : MModel S3 :=
    { carrier := fun _ => Bool
      nonempty := fun _ => ⟨false⟩
      interp := fun σ a =>
        match σ with
        | .f => ∅
        | .g => {a 0} }
  have hsat : M.Sat (φ3 (Var := Var) x y) := by
    apply hvalid M
    intro γ hγ
    exact hγ.elim
  let ρ : MVal M Var := fun _ _ => false
  have htotal := hsat ρ
  have hfalse : (false : Bool) ∈ mdenote M ρ (φ3 (Var := Var) x y) := by
    rw [htotal]
    trivial
  have hfalse' :
      ((∀ f : Fin 1 → Bool,
          f 0 = false → ∃ g : Fin 1 → Bool, g 0 = false) ∧
          (∀ f : Fin 1 → Bool, f 0 = false → f 0 = true) ∧
            ∀ f : Fin 1 → Bool,
              f 0 = true → f 0 = false → ∃ g : Fin 1 → Bool, g 0 = false) ∧
        (∀ f : Fin 1 → Bool,
          f 0 = true → f 0 = false → ∃ g : Fin 1 → Bool, g 0 = false) ∧
          ∀ f : Fin 1 → Bool, f 0 = true := by
    simpa [mdenote, MModel.app, mupdate, M, hxy] using hfalse
  have hcontra := hfalse'.2.2 (fun _ => false)
  exact Bool.noConfusion hcontra

/-- **Corollary 31**, at the Proposition 30 data.

The paper states Corollary 31 in general: *"There is no translation from
many-sorted definedness-free matching logic into any one-sorted definedness-free
matching logic that preserves global consequence and reflects derivability."*
Its proof is one line — preservation, then Corollary 15 in the target, then
reflection would give `Γ ⊢ φ`.

What is stated here is the **counterexample instance**, not the general
statement: there is no target signature and pair of translations that works for
the Proposition 30 data. A full rendering would define a translation on the
whole source language and state preservation and reflection generally; this is
the lemma that instance argument needs, and the general form is future work.

Three hypotheses are load-bearing and were all missing from a first draft of
this statement, which an audit showed to be concretely FALSE without them:

* `hxy : x ≠ y` — without it `φ3` collapses to a derivable pattern, and the
  existential body is inhabited;
* `StrongLocalCompleteness T Var` — (L) must hold **in the target**, since the
  paper's proof applies Corollary 15 there. A first draft required it of an
  unrelated fixed signature;
* closedness of the translated patterns, which `global_completeness` requires.
-/
theorem no_faithful_translation (hS : MSoundness S3 Var)
    (x y : Var) (hxy : x ≠ y) :
    ¬ ∃ (T : Signature) (tΓ : MPattern S3 Var Srt3.a → Pattern T Var)
        (tφ : MPattern S3 Var Srt3.c → Pattern T Var),
        StrongLocalCompleteness T Var ∧
        (∀ γ ∈ Γ3 (Var := Var) x y, Closed (tΓ γ)) ∧
        Closed (tφ (φ3 (Var := Var) x y)) ∧
        (MGlobalCons (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) →
          GlobalCons (tΓ '' Γ3 (Var := Var) x y) (tφ (φ3 (Var := Var) x y))) ∧
        (Provable (tΓ '' Γ3 (Var := Var) x y) (tφ (φ3 (Var := Var) x y)) →
          MProvable (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y)) := by
  rintro ⟨T, tΓ, tφ, hL, hclosedΓ, hclosedφ, hpreserve, hreflect⟩
  apply Γ3_not_derives_φ3 hS x y hxy
  apply hreflect
  apply (global_completeness_of_localCompleteness hL ?_ hclosedφ).mp
  · exact hpreserve (Γ3_entails_φ3 x y hxy)
  · intro δ hδ
    rcases hδ with ⟨γ, hγ, rfl⟩
    exact hclosedΓ γ hγ

end Sorted
end MatchingLogic
