/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Discon

/-! # Q-formulas and their normal form (Definitions 9.15, 9.16 and Fact 9.17)

The pre-interpolants of Definition 9.18 are not arbitrary formulas: they are built from
"ordinary" formulas and from *internal variables* `q_x`, one for each companion node `x`
of the quasi-tableau `Q`, using only conjunction and (sequences of) boxes.

Instead of using fresh proposition letters for the internal variables we use a separate
constructor `QFormula.var` of a new data type `QFormula Var`, where `Var` is the type of
internal variables. This makes the side condition of Definition 9.15 — that the
vocabulary of the ordinary formulas `ψ` and of the programs `αs` contains no internal
variables — true by construction, and it avoids having to pick fresh proposition letters.

To read a `QFormula` as an actual `Formula` one has to say what the internal variables
stand for. This is done by `QFormula.subst σ` where `σ : Var → Formula`. Taking
`σ x = ·(n x)` for an injection `n` into unused proposition letters gives the formulas of
the paper, but the extra generality is exactly what is needed later: in the correctness
proof the internal variables get replaced by other formulas.
-/

public section

namespace PDL

/-! ## Definition 9.15: the language `L_Q` -/

/-- Def 9.15: the set `L_Q` of *Q-formulas*, given by the grammar
`ι ::= ψ | q | ι ∧ ι | □(αs, ι)`.
Here `Var` is the type of internal variables, i.e. the paper's `{ q_x | x ∈ K_Q }`.
The side condition that `ψ` and `αs` contain no internal variables is automatic here
because internal variables are not `Formula`s. -/
inductive QFormula (Var : Type) : Type
  /-- An ordinary formula `ψ`, containing no internal variables. -/
  | fma : Formula → QFormula Var
  /-- An internal variable `q_x`. -/
  | var : Var → QFormula Var
  /-- A conjunction `ι₁ ∧ ι₂`. -/
  | and : QFormula Var → QFormula Var → QFormula Var
  /-- A box `□(αs, ι)` over a sequence of programs. -/
  | boxes : List Program → QFormula Var → QFormula Var
  deriving Repr, DecidableEq

namespace QFormula

variable {Var : Type}

/-- Replace the internal variables in a Q-formula according to `σ`, yielding a `Formula`.
For `σ x = ·(n x)` with `n` injective into unused proposition letters this is the formula
that the paper denotes by `ι` itself. -/
def subst (σ : Var → Formula) : QFormula Var → Formula
  | .fma ψ => ψ
  | .var q => σ q
  | .and ι1 ι2 => ι1.subst σ ⋀ ι2.subst σ
  | .boxes as ι => ⌈⌈as⌉⌉(ι.subst σ)

@[simp] lemma subst_fma {σ : Var → Formula} {ψ} : (fma ψ : QFormula Var).subst σ = ψ := rfl
@[simp] lemma subst_var {σ : Var → Formula} {q} : (var q : QFormula Var).subst σ = σ q := rfl
@[simp] lemma subst_and {σ : Var → Formula} {ι1 ι2 : QFormula Var} :
    (ι1.and ι2).subst σ = ι1.subst σ ⋀ ι2.subst σ := rfl
@[simp] lemma subst_boxes {σ : Var → Formula} {as} {ι : QFormula Var} :
    (ι.boxes as).subst σ = ⌈⌈as⌉⌉(ι.subst σ) := rfl

/-- The internal variables occurring in a Q-formula. -/
@[expose] def vars : QFormula Var → List Var
  | .fma _ => []
  | .var q => [q]
  | .and ι1 ι2 => ι1.vars ++ ι2.vars
  | .boxes _ ι => ι.vars

/-- Substitute the Q-formula `ρ` for the internal variable `x`. -/
def substVar [DecidableEq Var] (x : Var) (ρ : QFormula Var) (ι : QFormula Var) : QFormula Var :=
  match ι with
  | .fma ψ => .fma ψ
  | .var q => if q = x then ρ else .var q
  | .and ι1 ι2 => .and (substVar x ρ ι1) (substVar x ρ ι2)
  | .boxes as ι => .boxes as (substVar x ρ ι)
termination_by sizeOf ι

/-- Big conjunction of a list of Q-formulas, mirroring `con` on formulas. -/
@[expose] def conj : List (QFormula Var) → QFormula Var
  | [] => .fma ⊤
  | [ι] => ι
  | ι :: rest => .and ι (conj rest)

@[simp] lemma conj_nil : conj ([] : List (QFormula Var)) = .fma ⊤ := rfl
@[simp] lemma conj_singleton {ι : QFormula Var} : conj [ι] = ι := rfl

/-- Substitution commutes with big conjunction. -/
lemma subst_conj (σ : Var → Formula) :
    ∀ L : List (QFormula Var), (conj L).subst σ = con (L.map (subst σ))
  | [] => rfl
  | [_] => rfl
  | ι1 :: ι2 :: L => by
      have IH := subst_conj σ (ι2 :: L)
      simp only [conj, subst_and, IH, List.map_cons, con]

end QFormula

/-! ## Simple Q-formulas and Definition 9.16: the normal form -/

/-- A *simple* Q-formula (Def 9.15): either an ordinary formula `ψ` or a box `□(αs, q_x)`
over an internal variable. -/
inductive QSimple (Var : Type) : Type
  | fma : Formula → QSimple Var
  | boxVar : List Program → Var → QSimple Var
  deriving Repr, DecidableEq

namespace QSimple

variable {Var : Type}

/-- A simple Q-formula is a Q-formula. -/
@[expose] def toQ : QSimple Var → QFormula Var
  | .fma ψ => .fma ψ
  | .boxVar as q => .boxes as (.var q)

/-- Prefix a simple Q-formula with a sequence of boxes; the result is again simple. -/
@[expose] def prefixBoxes (as : List Program) : QSimple Var → QSimple Var
  | .fma ψ => .fma (⌈⌈as⌉⌉ψ)
  | .boxVar bs q => .boxVar (as ++ bs) q

@[simp] lemma toQ_prefixBoxes (as : List Program) (s : QSimple Var) (σ : Var → Formula) :
    (prefixBoxes as s).toQ.subst σ = ⌈⌈as⌉⌉(s.toQ.subst σ) := by
  cases s with
  | fma ψ => rfl
  | boxVar bs q =>
      simp only [prefixBoxes, toQ, QFormula.subst_boxes, QFormula.subst_var]
      induction as with
      | nil => rfl
      | cons a as IH => simp only [List.cons_append, Formula.boxes_cons, IH]

/-- Does the simple Q-formula mention the internal variable `x`? -/
@[expose] def mentions [DecidableEq Var] (x : Var) : QSimple Var → Bool
  | .fma _ => false
  | .boxVar _ q => q = x

/-- If the simple Q-formula is `□(αs, q_x)` then return the program `αs` as one program. -/
@[expose] def progToOpt [DecidableEq Var] (x : Var) : QSimple Var → Option Program
  | .fma _ => none
  | .boxVar as q => if q = x then some (Program.steps as) else none

end QSimple

namespace QFormula

variable {Var : Type}

/-- Def 9.16: the finite set `Spl(ι)` of simple Q-formulas of a Q-formula `ι`.
Note that `Spl(q_x) = { [⊤?]q_x }`, i.e. we make the variable into a box formula. -/
@[expose] def Spl : QFormula Var → List (QSimple Var)
  | .fma ψ => [.fma ψ]
  | .var q => [.boxVar [?'⊤] q]
  | .and ι1 ι2 => ι1.Spl ++ ι2.Spl
  | .boxes as ι => ι.Spl.map (QSimple.prefixBoxes as)

/-- `Spl(ι)` is never empty. -/
lemma Spl_ne_nil (ι : QFormula Var) : ι.Spl ≠ [] := by
  induction ι with
  | fma => simp [Spl]
  | var => simp [Spl]
  | and ι1 ι2 IH1 => simp [Spl, IH1]
  | boxes as ι IH => simpa [Spl] using IH

/-- Def 9.16: the normal form `ι^nf` of a Q-formula, the conjunction of `Spl(ι)`. -/
def nf (ι : QFormula Var) : QFormula Var := conj (ι.Spl.map QSimple.toQ)

/-- Being *in normal form*: a conjunction of simple Q-formulas. -/
def IsNormalForm (ι : QFormula Var) : Prop := ∃ L : List (QSimple Var), ι = conj (L.map QSimple.toQ)

lemma isNormalForm_nf (ι : QFormula Var) : IsNormalForm ι.nf := ⟨ι.Spl, rfl⟩

/-- Evaluating a normal form means evaluating all its simple conjuncts. -/
lemma eval_nf_iff {W} {M : KripkeModel W} {w : W} (σ : Var → Formula) (ι : QFormula Var) :
    evaluate M w (ι.nf.subst σ) ↔ ∀ s ∈ ι.Spl, evaluate M w (s.toQ.subst σ) := by
  rw [nf, subst_conj, conEval]
  simp only [List.mem_map, List.map_map, Function.comp_apply, forall_exists_index, and_imp]
  constructor
  · intro h s hs; exact h _ s hs rfl
  · rintro h _ s hs rfl; exact h s hs

/-! ## Fact 9.17 -/

/-- Fact 9.17, first part: every Q-formula is equivalent to its normal form. -/
theorem eval_nf {W} {M : KripkeModel W} {w : W} (σ : Var → Formula) (ι : QFormula Var) :
    evaluate M w (ι.nf.subst σ) ↔ evaluate M w (ι.subst σ) := by
  induction ι generalizing w with
  | fma ψ => simp [eval_nf_iff, Spl, QSimple.toQ]
  | var q => simp [eval_nf_iff, Spl, QSimple.toQ, evaluate, relate]
  | and ι1 ι2 IH1 IH2 =>
      rw [eval_nf_iff]
      simp only [Spl, List.mem_append, subst_and, evaluate]
      rw [← IH1 (w := w), ← IH2 (w := w), eval_nf_iff, eval_nf_iff]
      constructor
      · intro h; exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
      · rintro ⟨h1, h2⟩ s (hs | hs)
        · exact h1 s hs
        · exact h2 s hs
  | boxes as ι IH =>
      rw [eval_nf_iff]
      simp only [Spl, List.mem_map, subst_boxes, evalBoxes, forall_exists_index, and_imp]
      constructor
      · intro h v hv
        rw [← IH (w := v), eval_nf_iff]
        intro s hs
        have := h _ s hs rfl
        rw [QSimple.toQ_prefixBoxes, evalBoxes] at this
        exact this v hv
      · rintro h _ s hs rfl
        rw [QSimple.toQ_prefixBoxes, evalBoxes]
        intro v hv
        have hv' := h v hv
        rw [← IH (w := v), eval_nf_iff] at hv'
        exact hv' s hs

/-- The vocabulary of a simple Q-formula prefixed with boxes. -/
lemma voc_toQ_prefixBoxes (as : List Program) (s : QSimple Var) (σ : Var → Formula) :
    ((QSimple.prefixBoxes as s).toQ.subst σ).voc = as.pdlPvoc ∪ (s.toQ.subst σ).voc := by
  rw [QSimple.toQ_prefixBoxes, Formula.voc_boxes]

/-- The vocabulary of a normal form is the union of the vocabularies of its conjuncts. -/
lemma mem_voc_nf {n} (σ : Var → Formula) (ι : QFormula Var) :
    n ∈ (ι.nf.subst σ).voc ↔ ∃ s ∈ ι.Spl, n ∈ (s.toQ.subst σ).voc := by
  rw [nf, subst_conj, in_voc_con]
  simp only [List.mem_map, List.map_map, Function.comp_apply]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hn⟩; exact ⟨s, hs, hn⟩
  · rintro ⟨s, hs, hn⟩; exact ⟨_, ⟨s, hs, rfl⟩, hn⟩

/-- Fact 9.17, second part: a Q-formula and its normal form have the same vocabulary. -/
theorem voc_nf (σ : Var → Formula) (ι : QFormula Var) :
    (ι.nf.subst σ).voc = (ι.subst σ).voc := by
  apply Finset.ext
  intro n
  induction ι with
  | fma ψ => rw [mem_voc_nf]; simp [Spl, QSimple.toQ]
  | var q => rw [mem_voc_nf]; simp [Spl, QSimple.toQ, Formula.boxes]
  | and ι1 ι2 IH1 IH2 =>
      rw [mem_voc_nf] at IH1 IH2 ⊢
      simp only [Spl, List.mem_append, subst_and, Formula.voc, Finset.mem_union]
      grind
  | boxes as ι IH =>
      rw [mem_voc_nf] at IH ⊢
      simp only [Spl, List.mem_map, subst_boxes, Formula.voc_boxes, Finset.mem_union]
      constructor
      · rintro ⟨_, ⟨s, hs, rfl⟩, hn⟩
        rw [voc_toQ_prefixBoxes, Finset.mem_union] at hn
        rcases hn with hn | hn
        · exact Or.inl hn
        · exact Or.inr (IH.mp ⟨s, hs, hn⟩)
      · rintro (hn | hn)
        · obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (Spl_ne_nil ι)
          refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
          rw [voc_toQ_prefixBoxes]
          exact Finset.mem_union_left _ hn
        · obtain ⟨s, hs, hn⟩ := IH.mpr hn
          refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
          rw [voc_toQ_prefixBoxes]
          exact Finset.mem_union_right _ hn

/-! ## The fixpoint elimination used at companion nodes (part of Definition 9.18)

Given `ι` with normal form `⋀ᵢ [αᵢ]q_x ∧ ⋀ⱼ [βⱼ]q_{zⱼ} ∧ ψ`, the pre-interpolant of the
companion `x` is `[(⋃ᵢ αᵢ)*](⋀ⱼ [βⱼ]q_{zⱼ} ∧ ψ)`. We implement this here as
`QFormula.gfp x ι`, using `Spl` to read off the `αᵢ` and the remaining conjuncts. -/

/-- The programs `αᵢ` such that `[αᵢ]q_x` is a conjunct of the normal form of `ι`. -/
@[expose] def loopProgs [DecidableEq Var] (x : Var) (ι : QFormula Var) : List Program :=
  ι.Spl.filterMap (QSimple.progToOpt x)

/-- The conjunction of those conjuncts of the normal form of `ι` that do not mention the
internal variable `x`. -/
def dropVar [DecidableEq Var] (x : Var) (ι : QFormula Var) : QFormula Var :=
  conj ((ι.Spl.filter (fun s => !s.mentions x)).map QSimple.toQ)

/-- The greatest fixpoint of `ι` with respect to the internal variable `x`, i.e. the
formula `[(⋃ᵢ αᵢ)*](⋀ⱼ [βⱼ]q_{zⱼ} ∧ ψ)` of the companion case of Definition 9.18. -/
@[expose] def gfp [DecidableEq Var] (x : Var) (ι : QFormula Var) : QFormula Var :=
  .boxes [∗ (Program.unions (ι.loopProgs x))] (ι.dropVar x)

/-- The internal variable `x` no longer occurs in `gfp x ι`. -/
lemma not_mem_vars_gfp [DecidableEq Var] (x : Var) (ι : QFormula Var) :
    x ∉ (ι.gfp x).vars := by
  have main : ∀ L : List (QSimple Var), (∀ s ∈ L, ¬ s.mentions x) →
      x ∉ (conj (L.map QSimple.toQ)).vars := by
    intro L
    induction L with
    | nil => simp [vars]
    | cons s L IH =>
      intro h
      have hs : x ∉ s.toQ.vars := by
        cases s with
        | fma ψ => simp [QSimple.toQ, vars]
        | boxVar as q =>
            have hq : ¬ (q = x) := by
              have := h _ (List.mem_cons_self ..)
              simpa only [QSimple.mentions, decide_eq_true_eq] using this
            simp only [QSimple.toQ, vars, List.mem_singleton]
            exact fun h' => hq h'.symm
      have hL := IH (fun s hs => h s (List.mem_cons_of_mem _ hs))
      cases L with
      | nil => simpa using hs
      | cons t L => simp only [List.map_cons, conj, vars, List.mem_append, not_or]
                    exact ⟨hs, by simpa using hL⟩
  simp only [gfp, vars, dropVar]
  refine main _ ?_
  intro s hs
  simp only [List.mem_filter, Bool.not_eq_true'] at hs
  simp [hs.2]

end QFormula

end PDL
