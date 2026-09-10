/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.QuotientTermModel
import LeanPool.InfinitaryLogic.Methods.ConstantInstances
import LeanPool.InfinitaryLogic.Lomega1omega.Depth
import LeanPool.InfinitaryLogic.Lomega1omega.OpenBoundsSemantics
/-!
# The forward truth lemma for the quotient term model (issue #8, commit 5b)

From a Henkin-complete set `S` over the relational core `L[[ℕ]]`, `QuotientTermModel.lean` (commit
5a) built the closed-term quotient model `QModel hsc` and its **atomic** semantics.  This file lifts
that to the full **forward, polarity-sensitive truth lemma** and packages a consumer-shaped
model-existence theorem.

## Discipline

The truth lemma is **not** a biconditional `M ⊨ φ ↔ φ ∈ S`.  It is two *separate forward*
implications — one per polarity — proven **together** by a single simultaneous recursion:

* `truth_pos` : `σ ∈ S → M ⊨ σ`   (positive polarity)
* `truth_neg` : `σ.not ∈ S → ¬ M ⊨ σ`   (negative polarity)

No excluded middle / `by_cases` on membership `_ ∈ S`, and no maximality/decisiveness of `S`, is
used anywhere.  Every step is driven by a *constructive* `HenkinComplete` field:

* connectives — `imp` / `neg_imp` / `iInf` / `neg_iInf` / `iSup` / `neg_iSup`;
* quantifiers — `all_inst` (positive) and `neg_all_witness` (negative) **only**;
* atomics — the commit-5a quotient API (`qmk_eq_of_mem` / `qmk_ne_of_neg_mem` / `relMap_of_mem` /
  `not_relMap_of_neg_mem`), with the `Empty ⊕ Fin 0` sentence-term bridge below;
* contradictions — `no_falsum` / `no_contradiction` (`C0`).

## The `all` case (depth-measure recursion)

The quantifier cases are handled by **well-founded recursion on an ordinal depth measure**,
mirroring
the shape of the legacy `Methods/Henkin/Construction.lean` truth lemma: from `(all body) ∈ S` the
`all_inst` field yields, for every constant `c`, the sentence `instConst c body =
(body.openBounds).subst (fun _ => constTerm c)`, whose depth is strictly smaller than that of
`all body`; recursion on that sentence plus `realize_instConst_qmodel` and surjectivity of `qmk`
discharges the universal (dually for the negated universal via `neg_all_witness`).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} [L.IsRelational] {U S : Set L[[ℕ]].Sentenceω}

/-! ## The `Empty ⊕ Fin 0` sentence-term bridge

Sentence atomics `equal t u` / `rel R ts` carry terms in `L[[ℕ]].Term (Empty ⊕ Fin 0)`.  Since both
`Empty` and `Fin 0` are uninhabited, every such term is ground; we collapse it to
`L[[ℕ]].Term Empty`
(a re-statement of the private helpers in `Methods/Henkin/Construction.lean`). -/

/-- Collapse a sentence-atomic term (variables in the uninhabited `Empty ⊕ Fin 0`) to a closed
`Term Empty`. -/
private def Term.toGround : L[[ℕ]].Term (Empty ⊕ Fin 0) → L[[ℕ]].Term Empty
  | .var x => match x with
    | Sum.inl e => Empty.elim e
    | Sum.inr i => i.elim0
  | .func f ts => .func f (fun i => (ts i).toGround)

omit [L.IsRelational] in
/-- Relabeling a `toGround`-collapsed term back to `Empty ⊕ Fin 0` recovers the original. -/
private theorem Term.toGround_relabel_inl (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    (t.toGround).relabel (Sum.inl : Empty → Empty ⊕ Fin 0) = t := by
  induction t with
  | var x => rcases x with e | i
             · exact e.elim
             · exact i.elim0
  | func f ts ih => simp only [Term.toGround, Term.relabel]; congr 1; funext i; exact ih i

omit [L.IsRelational] in
/-- Evaluating a sentence-atomic term with any assignment equals evaluating its `toGround` collapse
with `Empty.elim` (both variable types are uninhabited). -/
private theorem Term.realize_toGround {M : Type*} [L[[ℕ]].Structure M]
    (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) (v : Empty ⊕ Fin 0 → M) :
    t.realize v = (t.toGround).realize (Empty.elim : Empty → M) := by
  induction t with
  | var x => rcases x with e | i
             · exact e.elim
             · exact i.elim0
  | func f ts ih => simp only [Term.toGround, Term.realize]; congr 1; funext i; exact ih i

/-! ## `closeBy` and its realization (validated commit-5b foundation) -/

/-- Realizing `closeBy φ τ` in `QModel hsc` is realizing `φ` at the classes of the constants `τ`. -/
theorem realize_closeBy (hsc : HenkinComplete U S) (φ : L[[ℕ]].BoundedFormulaω Empty n)
    (τ : Fin n → ℕ) :
    @Sentenceω.Realize L[[ℕ]] (closeBy φ τ) (QModel hsc) (qModelStructure hsc)
      ↔ @BoundedFormulaω.Realize L[[ℕ]] (QModel hsc) (qModelStructure hsc) Empty n φ Empty.elim
          (fun i => qmk hsc (constTerm (τ i))) := by
  change @BoundedFormulaω.Realize L[[ℕ]] (QModel hsc) (qModelStructure hsc) Empty 0 (closeBy φ τ)
      Empty.elim Fin.elim0 ↔ _
  rw [closeBy, BoundedFormulaω.realize_subst]
  rw [show (fun i => Term.realize (Empty.elim : Empty → QModel hsc) (constTerm (τ i)))
        = (fun i => qmk hsc (constTerm (τ i))) from funext fun i => qterm_realize_eq_mk hsc _]
  exact realize_openBounds φ (fun i => qmk hsc (constTerm (τ i)))

/-- The constant instance `instConst c body` realizes in `QModel hsc` exactly as `body` at the class
of `c` in its single variable.  This is the semantic bridge the `all` case consumes; it needs no
syntactic substitution-composition identity. -/
private theorem realize_instConst_qmodel (hsc : HenkinComplete U S)
    (body : L[[ℕ]].BoundedFormulaω Empty 1) (c : ℕ) :
    @Sentenceω.Realize L[[ℕ]] (instConst c body) (QModel hsc) (qModelStructure hsc)
      ↔ @BoundedFormulaω.Realize L[[ℕ]] (QModel hsc) (qModelStructure hsc) Empty 1 body Empty.elim
          (fun _ : Fin 1 => qmk hsc (constTerm c)) :=
  realize_closeBy hsc body (fun _ : Fin 1 => c)

/-! ## Surjectivity of the quotient map -/

/-- Every element of the quotient term model is the class of some constant. -/
private theorem qmk_surjective (hsc : HenkinComplete U S) (x : QModel hsc) :
    ∃ c : ℕ, x = qmk hsc (constTerm c) := by
  obtain ⟨t, ht⟩ := Quotient.exists_rep x
  obtain ⟨c, rfl⟩ := exists_eq_constTerm t
  exact ⟨c, ht.symm⟩

/-! ## Ordinal depth: strict decrease for the constant instance

The generic preservation/strict-decrease calculus for `BoundedFormulaω.depth` now lives in the
neutral `Lomega1omega/Depth.lean` (shared with `Methods/Henkin/Construction.lean`); only the
`instConst` combination is derived here. -/

omit [L.IsRelational]

/-- The constant instance of `body` has strictly smaller depth than `all body`. -/
private theorem depth_instConst_lt (body : L[[ℕ]].BoundedFormulaω Empty 1) (c : ℕ) :
    (instConst c body).depth < (BoundedFormulaω.all body).depth := by
  rw [instConst, depth_subst, depth_openBounds]
  exact depth_lt_all

/-! ## Two small realization bookkeeping facts -/

/-- A single-variable valuation built by `Fin.snoc` on the empty tuple is constant.

Stated at `default`, the empty tuple the sentence semantics actually supplies; it is
definitionally `Fin.elim0`, but `rw` needs the spelling the goal carries. -/
private theorem snoc_elim0_const {M : Type*} (y : M) :
    (Fin.snoc (default : Fin 0 → M) y : Fin 1 → M) = fun _ => y := by
  funext i
  rw [Fin.eq_zero i]
  rfl

variable [L.IsRelational]

/-- A ground sentence-atomic term is the standard constant term of its collapsed constant. -/
private theorem constTermS_qtConst_toGround (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    constTermS (qtConst t.toGround) = t := by
  rw [← constTerm_relabel_inl, ← eq_constTerm_qtConst, Term.toGround_relabel_inl]

/-! ## The simultaneous forward truth lemma

`truth_both hsc σ` bundles the two polarities.  It is a **single well-founded recursion** on
`σ.depth`: connectives recurse on structural subformulas (strictly smaller depth), and the `all`
case recurses on `instConst c body` (a sentence of strictly smaller depth). -/

/-- **The forward, polarity-sensitive truth lemma (bundled).**  For every sentence `σ`, membership
in `S` forces truth in `QModel hsc` (positive), and membership of `σ.not` forces falsity (negative).
Proven by one simultaneous well-founded recursion on the ordinal depth of `σ`. -/
private theorem truth_both (hsc : HenkinComplete U S) :
    (σ : L[[ℕ]].Sentenceω) →
      (σ ∈ S → @Sentenceω.Realize L[[ℕ]] σ (QModel hsc) (qModelStructure hsc)) ∧
      (σ.not ∈ S → ¬ @Sentenceω.Realize L[[ℕ]] σ (QModel hsc) (qModelStructure hsc))
  | .falsum =>
      ⟨fun hmem => absurd hmem hsc.no_falsum, fun _ => by simp [Sentenceω.realize_def]⟩
  | .equal t₁ t₂ => by
      refine ⟨fun hmem => ?_, fun hmem => ?_⟩
      · -- positive: `equal t₁ t₂ ∈ S` gives the equality of classes
        change t₁.realize (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0)
            = t₂.realize (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0)
        rw [Term.realize_toGround t₁, Term.realize_toGround t₂,
          qterm_realize_eq_mk hsc t₁.toGround, qterm_realize_eq_mk hsc t₂.toGround,
          eq_constTerm_qtConst t₁.toGround, eq_constTerm_qtConst t₂.toGround]
        refine qmk_eq_of_mem hsc _ _ ?_
        have heq : constEq (qtConst t₁.toGround) (qtConst t₂.toGround)
            = BoundedFormulaω.equal t₁ t₂ := by
          simp only [constEq, constTermS_qtConst_toGround]
        rw [heq]; exact hmem
      · -- negative: `(equal t₁ t₂).not ∈ S` gives the disequality of classes
        change ¬ t₁.realize (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0)
            = t₂.realize (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0)
        rw [Term.realize_toGround t₁, Term.realize_toGround t₂,
          qterm_realize_eq_mk hsc t₁.toGround, qterm_realize_eq_mk hsc t₂.toGround,
          eq_constTerm_qtConst t₁.toGround, eq_constTerm_qtConst t₂.toGround]
        refine qmk_ne_of_neg_mem hsc _ _ ?_
        have heq : (constEq (qtConst t₁.toGround) (qtConst t₂.toGround)).not
            = (BoundedFormulaω.equal t₁ t₂).not := by
          simp only [constEq, constTermS_qtConst_toGround]
        rw [heq]; exact hmem
  | .rel R ts => by
      rcases R with R | R
      · -- relation of the base language `L`
        set g : Fin _ → ℕ := fun i => qtConst (ts i).toGround with hg
        have hts : ts = fun i => constTermS (g i) := by
          funext i; rw [hg]; exact (constTermS_qtConst_toGround (ts i)).symm
        refine ⟨fun hmem => ?_, fun hmem => ?_⟩
        · -- positive: `rel (Sum.inl R) ts ∈ S` gives `RelMap`
          change (qModelStructure hsc).RelMap (Sum.inl R)
              (fun i => (ts i).realize (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0))
          have hval : (fun i => (ts i).realize
                (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0))
              = fun i => qmk hsc (constTerm (g i)) := by
            funext i
            rw [Term.realize_toGround (ts i), qterm_realize_eq_mk hsc (ts i).toGround,
              hg, eq_constTerm_qtConst (ts i).toGround]
          rw [hval]
          refine relMap_of_mem hsc R g ?_
          rw [relInst, ← hts]; exact hmem
        · -- negative: `(rel (Sum.inl R) ts).not ∈ S` gives `¬ RelMap`
          change ¬ (qModelStructure hsc).RelMap (Sum.inl R)
              (fun i => (ts i).realize (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0))
          have hval : (fun i => (ts i).realize
                (Sum.elim (Empty.elim : Empty → QModel hsc) Fin.elim0))
              = fun i => qmk hsc (constTerm (g i)) := by
            funext i
            rw [Term.realize_toGround (ts i), qterm_realize_eq_mk hsc (ts i).toGround,
              hg, eq_constTerm_qtConst (ts i).toGround]
          rw [hval]
          refine not_relMap_of_neg_mem hsc R g ?_
          rw [relInst, ← hts]; exact hmem
      · exact isEmptyElim R
  | .imp φ ψ => by
      refine ⟨fun hmem hφ => ?_, fun hmem hif => ?_⟩
      · -- positive: C1
        rcases hsc.imp φ ψ hmem with hn | hy
        · exact absurd hφ ((truth_both hsc φ).2 hn)
        · exact (truth_both hsc ψ).1 hy
      · -- negative: C1'
        obtain ⟨hφmem, hψnmem⟩ := hsc.neg_imp φ ψ hmem
        exact (truth_both hsc ψ).2 hψnmem (hif ((truth_both hsc φ).1 hφmem))
  | .iInf φs => by
      refine ⟨fun hmem k => ?_, fun hmem hall => ?_⟩
      · -- positive: C3
        exact (truth_both hsc (φs k)).1 (hsc.iInf φs hmem k)
      · -- negative: C3'
        obtain ⟨k, hk⟩ := hsc.neg_iInf φs hmem
        exact (truth_both hsc (φs k)).2 hk (hall k)
  | .iSup φs => by
      refine ⟨fun hmem => ?_, fun hmem hex => ?_⟩
      · -- positive: C4
        obtain ⟨k, hk⟩ := hsc.iSup φs hmem
        exact ⟨k, (truth_both hsc (φs k)).1 hk⟩
      · -- negative: C4'
        obtain ⟨k, hk⟩ := hex
        exact (truth_both hsc (φs k)).2 (hsc.neg_iSup φs hmem k) hk
  | .all body => by
      refine ⟨fun hmem x => ?_, fun hmem hall => ?_⟩
      · -- positive: universal instantiation (`all_inst`) + surjectivity of `qmk`
        obtain ⟨c, rfl⟩ := qmk_surjective hsc x
        have hreal := (truth_both hsc (instConst c body)).1 (hsc.all_inst body hmem c)
        rw [realize_instConst_qmodel hsc body c] at hreal
        rw [snoc_elim0_const]
        exact hreal
      · -- negative: fresh witness for the negated universal (`neg_all_witness`)
        obtain ⟨c, hc⟩ := hsc.neg_all_witness body hmem
        have hnreal := (truth_both hsc (instConst c body)).2 hc
        rw [realize_instConst_qmodel hsc body c] at hnreal
        refine hnreal ?_
        have h := hall (qmk hsc (constTerm c))
        rwa [snoc_elim0_const] at h
  termination_by σ => σ.depth
  decreasing_by
    all_goals first
      | exact depth_lt_imp_left
      | exact depth_lt_imp_right
      | exact depth_lt_iSup _
      | exact depth_lt_iInf _
      | exact depth_instConst_lt _ _

/-! ## The consumer model-existence theorem -/

/-- **Model existence from a Henkin-complete set.**  The quotient term model is a nonempty
`L[[ℕ]]`-structure realizing every member of `S` and falsifying every sentence whose negation is in
`S`.  Both polarities are exposed for members of `S`. -/
theorem exists_model_of_henkinComplete (hsc : HenkinComplete U S) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      (∀ φ : L[[ℕ]].Sentenceω, φ ∈ S → Sentenceω.Realize φ M) ∧
      (∀ φ : L[[ℕ]].Sentenceω, φ.not ∈ S → ¬ Sentenceω.Realize φ M) :=
  ⟨QModel hsc, qModelStructure hsc, ⟨qmk hsc (constTerm 0)⟩,
    fun φ => (truth_both hsc φ).1, fun φ => (truth_both hsc φ).2⟩

end FirstOrder.Language
